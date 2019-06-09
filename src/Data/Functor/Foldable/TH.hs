{-# LANGUAGE CPP, Rank2Types #-}
module Data.Functor.Foldable.TH
  ( makeBaseFunctor
  , makeBaseFunctorWith
  , BaseRules
  , baseRules
  , baseRulesType
  , baseRulesCon
  , baseRulesField
  ) where

import Control.Applicative as A
import Control.Monad
import Data.Traversable as T
import Data.Functor.Identity
import Language.Haskell.TH
import Language.Haskell.TH.Datatype as TH.Abs
import Language.Haskell.TH.Syntax (mkNameG_tc, mkNameG_v)
import Data.Char (GeneralCategory (..), generalCategory)
import Data.Orphans ()
#ifndef CURRENT_PACKAGE_KEY
import Data.Version (showVersion)
import Paths_recursion_schemes (version)
#endif

-- | Build base functor with a sensible default configuration.
--
-- /e.g./
--
-- @
-- data Expr a
--     = Lit a
--     | Add (Expr a) (Expr a)
--     | Expr a :* [Expr a]
--   deriving (Show)
--
-- 'makeBaseFunctor' ''Expr
-- @
--
-- will create
--
-- @
-- data ExprF a x
--     = LitF a
--     | AddF x x
--     | x :*$ [x]
--   deriving ('Functor', 'Foldable', 'Traversable')
--
-- type instance 'Base' (Expr a) = ExprF a
--
-- instance 'Recursive' (Expr a) where
--     'project' (Lit x)   = LitF x
--     'project' (Add x y) = AddF x y
--     'project' (x :* y)  = x :*$ y
--
-- instance 'Corecursive' (Expr a) where
--     'embed' (LitF x)   = Lit x
--     'embed' (AddF x y) = Add x y
--     'embed' (x :*$ y)  = x :* y
-- @
--
-- @
-- 'makeBaseFunctor' = 'makeBaseFunctorWith' 'baseRules'
-- @
--
-- /Notes:/
--
-- 'makeBaseFunctor' works properly only with ADTs.
-- Existentials and GADTs aren't supported,
-- as we don't try to do better than
-- <https://downloads.haskell.org/~ghc/latest/docs/html/users_guide/glasgow_exts.html#deriving-functor-instances GHC's DeriveFunctor>.
--
makeBaseFunctor :: Name -> DecsQ
makeBaseFunctor = makeBaseFunctorWith baseRules

-- | Build base functor with a custom configuration.
makeBaseFunctorWith :: BaseRules -> Name -> DecsQ
makeBaseFunctorWith rules name = reifyDatatype name >>= makePrimForDI rules

-- | Rules of renaming data names
data BaseRules = BaseRules
    { _baseRulesType  :: Name -> Name
    , _baseRulesCon   :: Name -> Name
    , _baseRulesField :: Name -> Name
    }

-- | Default 'BaseRules': append @F@ or @$@ to data type, constructors and field names.
baseRules :: BaseRules
baseRules = BaseRules
    { _baseRulesType  = toFName
    , _baseRulesCon   = toFName
    , _baseRulesField = toFName
    }

-- | How to name the base functor type.
--
-- Default is to append @F@ or @$@.
baseRulesType :: Functor f => ((Name -> Name) -> f (Name -> Name)) -> BaseRules -> f BaseRules
baseRulesType f rules = (\x -> rules { _baseRulesType = x }) <$> f (_baseRulesType rules)

-- | How to rename the base functor type constructors.
--
-- Default is to append @F@ or @$@.
baseRulesCon :: Functor f => ((Name -> Name) -> f (Name -> Name)) -> BaseRules -> f BaseRules
baseRulesCon f rules = (\x -> rules { _baseRulesCon = x }) <$> f (_baseRulesCon rules)

-- | How to rename the base functor type field names (in records).
--
-- Default is to append @F@ or @$@.
baseRulesField :: Functor f => ((Name -> Name) -> f (Name -> Name)) -> BaseRules -> f BaseRules
baseRulesField f rules = (\x -> rules { _baseRulesField = x }) <$> f (_baseRulesField rules)

toFName :: Name -> Name
toFName = mkName . f . nameBase
  where
    f name | isInfixName name = name ++ "$"
           | otherwise        = name ++ "F"

    isInfixName :: String -> Bool
    isInfixName = all isSymbolChar

makePrimForDI :: BaseRules -> DatatypeInfo -> DecsQ
makePrimForDI rules
  (DatatypeInfo { datatypeName      = tyName
                , datatypeInstTypes = instTys
                , datatypeCons      = cons
                , datatypeVariant   = variant }) = do
    when isDataFamInstance $
      fail "makeBaseFunctor: Data families are currently not supported."
    makePrimForDI' rules (variant == Newtype) tyName
                   (map toTyVarBndr instTys) cons
  where
    isDataFamInstance = case variant of
                          DataInstance    -> True
                          NewtypeInstance -> True
                          Datatype        -> False
                          Newtype         -> False

    toTyVarBndr :: Type -> TyVarBndr
    toTyVarBndr (VarT n)          = PlainTV n
    toTyVarBndr (SigT (VarT n) k) = KindedTV n k
    toTyVarBndr _                 = error "toTyVarBndr"

makePrimForDI' :: BaseRules -> Bool -> Name -> [TyVarBndr]
               -> [ConstructorInfo] -> DecsQ
makePrimForDI' rules isNewtype tyName vars cons = do
    -- variable parameters
    let vars' = map VarT (typeVars vars)
    -- Name of base functor
    let tyNameF = _baseRulesType rules tyName
    -- Recursive type
    let s = conAppsT tyName vars'
    -- Additional argument
    rName <- newName "r"
    let r = VarT rName
    -- Vars
    let varsF = vars ++ [PlainTV rName]

    -- #33
    cons' <- traverse (conTypeTraversal resolveTypeSynonyms) cons
    let consF
          = toCon
          . conNameMap (_baseRulesCon rules)
          . conFieldNameMap (_baseRulesField rules)
          . conTypeMap (substType s r)
          <$> cons'

    -- Data definition
    let dataDec = case consF of
#if MIN_VERSION_template_haskell(2,11,0)
            [conF] | isNewtype ->
                NewtypeD [] tyNameF varsF Nothing conF deriveds
            _ ->
                DataD [] tyNameF varsF Nothing consF deriveds
#else
            [conF] | isNewtype ->
                NewtypeD [] tyNameF varsF conF deriveds
            _ ->
                DataD [] tyNameF varsF consF deriveds
#endif
          where
            deriveds =
#if MIN_VERSION_template_haskell(2,12,0)
              [DerivClause Nothing
                [ ConT functorTypeName
                , ConT foldableTypeName
                , ConT traversableTypeName ]]
#elif MIN_VERSION_template_haskell(2,11,0)
              [ ConT functorTypeName
              , ConT foldableTypeName
              , ConT traversableTypeName ]
#else
              [functorTypeName, foldableTypeName, traversableTypeName]
#endif

    -- type instance Base
    baseDec <- tySynInstDCompat baseTypeName Nothing
                                [pure s] (pure $ conAppsT tyNameF vars')

    -- instance Recursive
    projDec <- FunD projectValName <$> mkMorphism id (_baseRulesCon rules) cons'
#if MIN_VERSION_template_haskell(2,11,0)
    let recursiveDec = InstanceD Nothing [] (ConT recursiveTypeName `AppT` s) [projDec]
#else
    let recursiveDec = InstanceD [] (ConT recursiveTypeName `AppT` s) [projDec]
#endif

    -- instance Corecursive
    embedDec <- FunD embedValName <$> mkMorphism (_baseRulesCon rules) id cons'
#if MIN_VERSION_template_haskell(2,11,0)
    let corecursiveDec = InstanceD Nothing [] (ConT corecursiveTypeName `AppT` s) [embedDec]
#else
    let corecursiveDec = InstanceD [] (ConT corecursiveTypeName `AppT` s) [embedDec]
#endif

    -- Combine
    A.pure [dataDec, baseDec, recursiveDec, corecursiveDec]

-- | makes clauses to rename constructors
mkMorphism
    :: (Name -> Name)
    -> (Name -> Name)
    -> [ConstructorInfo]
    -> Q [Clause]
mkMorphism nFrom nTo args = for args $ \ci -> do
    let n = constructorName ci
    fs <- replicateM (length (constructorFields ci)) (newName "x")
    pure $ Clause [ConP (nFrom n) (map VarP fs)]                      -- patterns
                  (NormalB $ foldl AppE (ConE $ nTo n) (map VarE fs)) -- body
                  [] -- where dec

-------------------------------------------------------------------------------
-- Traversals
-------------------------------------------------------------------------------

conNameTraversal :: Traversal' ConstructorInfo Name
conNameTraversal = lens constructorName (\s v -> s { constructorName = v })

conFieldNameTraversal :: Traversal' ConstructorInfo Name
conFieldNameTraversal = lens constructorVariant (\s v -> s { constructorVariant = v })
                      . conVariantTraversal
  where
    conVariantTraversal :: Traversal' ConstructorVariant Name
    conVariantTraversal _ NormalConstructor      = pure NormalConstructor
    conVariantTraversal _ InfixConstructor       = pure InfixConstructor
    conVariantTraversal f (RecordConstructor fs) = RecordConstructor <$> traverse f fs

conTypeTraversal :: Traversal' ConstructorInfo Type
conTypeTraversal = lens constructorFields (\s v -> s { constructorFields = v })
                 . traverse

conNameMap :: (Name -> Name) -> ConstructorInfo -> ConstructorInfo
conNameMap = over conNameTraversal

conFieldNameMap :: (Name -> Name) -> ConstructorInfo -> ConstructorInfo
conFieldNameMap = over conFieldNameTraversal

conTypeMap :: (Type -> Type) -> ConstructorInfo -> ConstructorInfo
conTypeMap = over conTypeTraversal

-------------------------------------------------------------------------------
-- Lenses
-------------------------------------------------------------------------------

type Lens'      s a = forall f. Functor     f => (a -> f a) -> s -> f s
type Traversal' s a = forall f. Applicative f => (a -> f a) -> s -> f s

lens :: (s -> a) -> (s -> a -> s) -> Lens' s a
lens sa sas afa s = sas s <$> afa (sa s)
{-# INLINE lens #-}

over :: Traversal' s a -> (a -> a) -> s -> s
over l f = runIdentity . l (Identity . f)
{-# INLINE over #-}

-------------------------------------------------------------------------------
-- Type mangling
-------------------------------------------------------------------------------

-- | Extract type variables
typeVars :: [TyVarBndr] -> [Name]
typeVars = map tvName

-- | Apply arguments to a type constructor.
conAppsT :: Name -> [Type] -> Type
conAppsT conName = foldl AppT (ConT conName)

-- | Provides substitution for types
substType
    :: Type
    -> Type
    -> Type
    -> Type
substType a b = go
  where
    go x | x == a         = b
    go (VarT n)           = VarT n
    go (AppT l r)         = AppT (go l) (go r)
    go (ForallT xs ctx t) = ForallT xs ctx (go t)
    -- This may fail with kind error
    go (SigT t k)         = SigT (go t) k
#if MIN_VERSION_template_haskell(2,11,0)
    go (InfixT l n r)     = InfixT (go l) n (go r)
    go (UInfixT l n r)    = UInfixT (go l) n (go r)
    go (ParensT t)        = ParensT (go t)
#endif
    -- Rest are unchanged
    go x = x

toCon :: ConstructorInfo -> Con
toCon (ConstructorInfo { constructorName       = name
                       , constructorVars       = vars
                       , constructorContext    = ctxt
                       , constructorFields     = ftys
                       , constructorStrictness = fstricts
                       , constructorVariant    = variant })
  | not (null vars && null ctxt)
  = error "makeBaseFunctor: GADTs are not currently supported."
  | otherwise
  = let bangs = map toBang fstricts
     in case variant of
          NormalConstructor        -> NormalC name $ zip bangs ftys
          RecordConstructor fnames -> RecC name $ zip3 fnames bangs ftys
          InfixConstructor         -> let [bang1, bang2] = bangs
                                          [fty1,  fty2]  = ftys
                                       in InfixC (bang1, fty1) name (bang2, fty2)
  where
#if MIN_VERSION_template_haskell(2,11,0)
    toBang (FieldStrictness upkd strct) = Bang (toSourceUnpackedness upkd)
                                               (toSourceStrictness strct)
      where
        toSourceUnpackedness :: Unpackedness -> SourceUnpackedness
        toSourceUnpackedness UnspecifiedUnpackedness = NoSourceUnpackedness
        toSourceUnpackedness NoUnpack                = SourceNoUnpack
        toSourceUnpackedness Unpack                  = SourceUnpack

        toSourceStrictness :: Strictness -> SourceStrictness
        toSourceStrictness UnspecifiedStrictness = NoSourceStrictness
        toSourceStrictness Lazy                  = SourceLazy
        toSourceStrictness TH.Abs.Strict         = SourceStrict
#else
    -- On old versions of Template Haskell, there isn't as rich of strictness
    -- information available, so the conversion is somewhat lossy. We try our
    -- best to recognize certain common combinations, and fall back to NotStrict
    -- in the event there's an exotic combination.
    toBang (FieldStrictness UnspecifiedUnpackedness Strict)                = IsStrict
    toBang (FieldStrictness UnspecifiedUnpackedness UnspecifiedStrictness) = NotStrict
    toBang (FieldStrictness Unpack Strict)                                 = Unpacked
    toBang FieldStrictness{}                                               = NotStrict
#endif

-------------------------------------------------------------------------------
-- Compat from base-4.9
-------------------------------------------------------------------------------

isSymbolChar :: Char -> Bool
isSymbolChar c = not (isPuncChar c) && case generalCategory c of
    MathSymbol              -> True
    CurrencySymbol          -> True
    ModifierSymbol          -> True
    OtherSymbol             -> True
    DashPunctuation         -> True
    OtherPunctuation        -> c `notElem` "'\""
    ConnectorPunctuation    -> c /= '_'
    _                       -> False

isPuncChar :: Char -> Bool
isPuncChar c = c `elem` ",;()[]{}`"

-------------------------------------------------------------------------------
-- Manually quoted names
-------------------------------------------------------------------------------
-- By manually generating these names we avoid needing to use the
-- TemplateHaskell language extension when compiling this library.
-- This allows the library to be used in stage1 cross-compilers.

rsPackageKey :: String
#ifdef CURRENT_PACKAGE_KEY
rsPackageKey = CURRENT_PACKAGE_KEY
#else
rsPackageKey = "recursion-schemes-" ++ showVersion version
#endif

mkRsName_tc :: String -> String -> Name
mkRsName_tc = mkNameG_tc rsPackageKey

mkRsName_v :: String -> String -> Name
mkRsName_v = mkNameG_v rsPackageKey

baseTypeName :: Name
baseTypeName = mkRsName_tc "Data.Functor.Foldable" "Base"

recursiveTypeName :: Name
recursiveTypeName = mkRsName_tc "Data.Functor.Foldable" "Recursive"

corecursiveTypeName :: Name
corecursiveTypeName = mkRsName_tc "Data.Functor.Foldable" "Corecursive"

projectValName :: Name
projectValName = mkRsName_v "Data.Functor.Foldable" "project"

embedValName :: Name
embedValName = mkRsName_v "Data.Functor.Foldable" "embed"

functorTypeName :: Name
functorTypeName = mkNameG_tc "base" "GHC.Base" "Functor"

foldableTypeName :: Name
foldableTypeName = mkNameG_tc "base" "Data.Foldable" "Foldable"

traversableTypeName :: Name
traversableTypeName = mkNameG_tc "base" "Data.Traversable" "Traversable"
