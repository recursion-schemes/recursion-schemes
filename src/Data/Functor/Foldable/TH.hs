{-# LANGUAGE CPP, PatternGuards, Rank2Types #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
module Data.Functor.Foldable.TH
  ( MakeBaseFunctor(..)
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
import Language.Haskell.TH.Datatype.TyVarBndr
import Language.Haskell.TH.Syntax (mkNameG_tc, mkNameG_v)
import qualified Language.Haskell.TH.PprLib as Ppr
import Data.Char (GeneralCategory (..), generalCategory)
import Data.Orphans ()
#ifndef CURRENT_PACKAGE_KEY
import Data.Version (showVersion)
import Paths_recursion_schemes (version)
#endif

#ifdef __HADDOCK__
import Data.Functor.Foldable
#endif

-- $setup
-- >>> :set -XTemplateHaskell -XTypeFamilies -XDeriveTraversable -XScopedTypeVariables
-- >>> import Data.Functor.Foldable

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
--
-- /Notes:/
--
-- 'makeBaseFunctor' works properly only with ADTs.
-- Existentials and GADTs aren't supported,
-- as we don't try to do better than
-- <https://downloads.haskell.org/~ghc/latest/docs/html/users_guide/glasgow_exts.html#deriving-functor-instances GHC's DeriveFunctor>.
--
-- 'makeBaseFunctor' can accept either of the following:
--
-- 1. A name
-- 2. A single declaration quote containing one or more empty instances
--
-- Allowing 'makeBaseFunctor' to take both 'Name's and 'Dec's is why it exists
-- as a method in a type class.  For trickier data-types, like rose-tree (see
-- also 'Cofree'):
--
-- @
-- data Rose f a = Rose a (f (Rose f a))
-- @
--
-- we can invoke 'makeBaseFunctor' with an instance declaration
-- to provide needed context for instances. (c.f. @StandaloneDeriving@)
--
-- @
-- 'makeBaseFunctor' [d| instance Functor f => Recursive (Rose f a) |]
-- @
--
-- will create
--
-- @
-- data RoseF f a r = RoseF a (f fr)
--   deriving ('Functor', 'Foldable', 'Traversable')
--
-- type instance 'Base' (Rose f a) = RoseF f a
--
-- instance Functor f => 'Recursive' (Rose f a) where
--   'project' (Rose x xs) = RoseF x xs
--
-- instance Functor f => 'Corecursive' (Rose f a) where
--   'embed' (RoseF x xs) = Rose x xs
-- @
--
-- Some doctests:
--
-- >>> data Expr a = Lit a | Add (Expr a) (Expr a) | Expr a :* [Expr a]; makeBaseFunctor ''Expr
--
-- >>> :t AddF
-- AddF :: r -> r -> ExprF a r
--
-- >>> data Rose f a = Rose a (f (Rose f a)); makeBaseFunctor [d| instance Functor f => Recursive (Rose f a) |]
--
-- >>> :t RoseF
-- RoseF :: a -> f r -> RoseF f a r
--
-- >>> let rose = Rose 1 (Just (Rose 2 (Just (Rose 3 Nothing))))
-- >>> cata (\(RoseF x f) -> x + maybe 0 id f) rose
-- 6
--
class MakeBaseFunctor a where
    -- |
    -- @
    -- 'makeBaseFunctor' = 'makeBaseFunctorWith' 'baseRules'
    -- @
    makeBaseFunctor :: a -> DecsQ
    makeBaseFunctor = makeBaseFunctorWith baseRules

    -- | Build base functor with a custom configuration.
    makeBaseFunctorWith :: BaseRules -> a -> DecsQ

instance MakeBaseFunctor Name where
    makeBaseFunctorWith rules name = reifyDatatype name >>= makePrimForDI rules Nothing

-- | Expects one or more declarations of 'Recursive' or 'Corecursive' instances, e.g.
--
-- @
-- makeBaseFunctor [d| instance Functor f => Recursive (Rose f a) |]
-- makeBaseFunctor [d|
--   instance C a => Recursive (Foo a b)
--   instance D a => Corecursive (Bar a b)
--   |]
-- @
--
-- This way we can provide a context for generated instances.
-- Note that this instance's 'makeBaseFunctor' still generates all of
-- 'Base' type instance, 'Recursive' and 'Corecursive' instances,
-- whether the user supplies a 'Recursive' or 'Corecursive' declaration.
instance (m ~ Q, x ~ [Dec]) => MakeBaseFunctor (m x) where
    makeBaseFunctorWith rules a = do
      user_decs <- a
      decs <- T.traverse (makeBaseFunctorDecWith rules) user_decs
      pure (concat decs)

-- The underlying implementation of MakeBaseFuctor (Q [Dec])
makeBaseFunctorDecWith :: BaseRules -> Dec -> DecsQ
makeBaseFunctorDecWith = go
  where
#if MIN_VERSION_template_haskell(2,11,0)
    go rules arg@(InstanceD overlaps ctx classHead []) = do
        let instanceFor = InstanceD overlaps ctx
#else
    go rules arg@(InstanceD ctx classHead []) = do
        let instanceFor = InstanceD ctx
#endif
        case classHead of
          ConT u `AppT` t | u == recursiveTypeName || u == corecursiveTypeName -> do
              name <- headOfType t
              di <- reifyDatatype name
              makePrimForDI rules (Just $ \n -> instanceFor (ConT n `AppT` t)) di
          _ -> err arg
    go _ arg = err arg

    -- This pretty printing is a bit hacky. Can we do better?
    err arg = fail . show $ Ppr.sep
      [ Ppr.space
      , Ppr.hang (Ppr.text "makeBaseFunctor: expected an instance head like") 4 $
          Ppr.text "`[d| instance ctx => Recursive (T a b ...) |]'"
      , Ppr.hang (Ppr.text "got") 4 $ Ppr.hcat
          [Ppr.text "`", ppr arg, Ppr.text "'"]
      ]

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

makePrimForDI :: BaseRules
              -> Maybe (Name -> [Dec] -> Dec) -- ^ make instance
              -> DatatypeInfo
              -> DecsQ
makePrimForDI rules mkInstance'
  (DatatypeInfo { datatypeName      = tyName
                , datatypeInstTypes = instTys
                , datatypeCons      = cons
                , datatypeVariant   = variant }) = do
    when isDataFamInstance $
      fail "makeBaseFunctor: Data families are currently not supported."
    makePrimForDI' rules mkInstance'
                   (variant == Newtype) tyName
                   (map toTyVarBndr instTys) cons
  where
    isDataFamInstance = case variant of
                          DataInstance    -> True
                          NewtypeInstance -> True
                          Datatype        -> False
                          Newtype         -> False

    toTyVarBndr :: Type -> TyVarBndrUnit
    toTyVarBndr (VarT n)          = plainTV n
    toTyVarBndr (SigT (VarT n) k) = kindedTV n k
    toTyVarBndr _                 = error "toTyVarBndr"

makePrimForDI' :: BaseRules
               -> Maybe (Name -> [Dec] -> Dec) -- ^ make instance
               -> Bool -> Name -> [TyVarBndrUnit]
               -> [ConstructorInfo] -> DecsQ
makePrimForDI' rules mkInstance' isNewtype tyName vars cons = do
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
    let varsF = vars ++ [plainTV rName]

    -- #33
    cons' <- traverse (conTypeTraversal resolveTypeSynonyms) cons
    let consF
          = toCon
          . conNameMap (_baseRulesCon rules)
          . conFieldNameMap (_baseRulesField rules)
          . conTypeMap (substType s r)
          <$> cons'

    -- Data definition
#if MIN_VERSION_template_haskell(2,12,0)
    derivStrat <- do
      e <- isExtEnabled DerivingStrategies
      pure $ if e then Just StockStrategy else Nothing
#endif
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
              [DerivClause derivStrat
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

    let mkInstance :: Name -> [Dec] -> Dec
        mkInstance = case mkInstance' of
            Just f  -> f
            Nothing -> \n ->
#if MIN_VERSION_template_haskell(2,11,0)
                InstanceD Nothing [] (ConT n `AppT` s)
#else
                InstanceD [] (ConT n `AppT` s)
#endif

    -- instance Recursive
    projDec <- FunD projectValName <$> mkMorphism id (_baseRulesCon rules) cons'
    let recursiveDec = mkInstance recursiveTypeName [projDec]

    -- instance Corecursive
    embedDec <- FunD embedValName <$> mkMorphism (_baseRulesCon rules) id cons'
    let corecursiveDec = mkInstance corecursiveTypeName [embedDec]

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
#if MIN_VERSION_template_haskell(2,18,0)
    pure $ Clause [ConP (nFrom n) [] (map VarP fs)]                   -- patterns
#else
    pure $ Clause [ConP (nFrom n) (map VarP fs)]                      -- patterns
#endif
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

headOfType :: Type -> Q Name
headOfType (AppT t _) = headOfType t
headOfType (VarT n)   = return n
headOfType (ConT n)   = return n
headOfType t          = fail $ "headOfType: " ++ show t

-- | Extract type variables
typeVars :: [TyVarBndr_ flag] -> [Name]
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
          InfixConstructor
            |  [bang1, bang2] <- bangs
            ,  [fty1,  fty2]  <- ftys
            -> InfixC (bang1, fty1) name (bang2, fty2)

            |  otherwise
            -> error $ "makeBaseFunctor: Encountered an InfixConstructor "
                    ++ "without exactly two fields"
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
