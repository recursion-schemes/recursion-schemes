{-# LANGUAGE CPP, PatternGuards, Rank2Types #-}
{-# LANGUAGE TemplateHaskellQuotes #-}
-- This OPTIONS_GHC line is a workaround for
-- https://gitlab.haskell.org/ghc/ghc/-/issues/18320, a bug which only occurs
-- when running specific TemplateHaskell code while both profiling and
-- optimisations are enabled. The code in this file triggers the bug, so until
-- it is fixed, we work around the issue by disabling optimisations in this
-- file. The code in this file only runs at compile-time, the code _generated_
-- by makeBaseFunctor will still get optimized if the file which calls
-- makeBaseFunctor is optimized.
{-# OPTIONS_GHC -O0 #-}
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
import Data.Char (GeneralCategory (..), generalCategory)

import Data.Functor.Foldable

#if !MIN_VERSION_template_haskell(2,21,0) && !MIN_VERSION_th_abstraction(0,6,0)
type TyVarBndrVis = TyVarBndrUnit
#endif

-- $setup
-- >>> :set -XTemplateHaskell -XTypeFamilies -XDeriveTraversable -XScopedTypeVariables
-- >>> import Data.Functor.Foldable
-- >>> import Language.Haskell.TH (Q)
-- >>> let asQ :: Q a -> Q a; asQ = id

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
-- Allowing 'makeBaseFunctor' to take both 'Name's and 'Dec's as an argument is why it exists as a method in a type class.
-- For trickier data-types, like rose-tree (see also 'Cofree'):
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
-- >>> data Rose f a = Rose a (f (Rose f a)); makeBaseFunctor $ asQ [d| instance Functor f => Recursive (Rose f a) |]
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

instance MakeBaseFunctor a => MakeBaseFunctor [a] where
    makeBaseFunctorWith rules a = fmap concat (T.traverse (makeBaseFunctorWith rules) a)

instance MakeBaseFunctor a => MakeBaseFunctor (Q a) where
    makeBaseFunctorWith rules a = makeBaseFunctorWith rules =<< a

instance MakeBaseFunctor Name where
    makeBaseFunctorWith rules name = reifyDatatype name >>= makePrimForDI rules Nothing

-- | Expects declarations of 'Recursive' or 'Corecursive' instances, e.g.
--
-- @
-- makeBaseFunctor [d| instance Functor f => Recursive (Rose f a) |]
-- @
--
-- This way we can provide a context for generated instances.
-- Note that this instance's 'makeBaseFunctor' still generates all of
-- 'Base' type instance, 'Recursive' and 'Corecursive' instances.
--
instance MakeBaseFunctor Dec where
    makeBaseFunctorWith rules (InstanceD overlaps ctx classHead []) = do
        let instanceFor = InstanceD overlaps ctx
        case classHead of
          ConT u `AppT` t | u == recursiveTypeName || u == corecursiveTypeName -> do
              name <- headOfType t
              di <- reifyDatatype name
              makePrimForDI rules (Just $ \n -> instanceFor (ConT n `AppT` t)) di
          _ -> fail $ "makeBaseFunctor: expected an instance head like `ctx => Recursive (T a b ...)`, got " ++ show classHead

    makeBaseFunctorWith _ _ = fail "makeBaseFunctor(With): expected an empty instance declaration"

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
    checkAllowed
    makePrimForDI' rules mkInstance'
                   (variant == Newtype) tyName
                   (map toTyVarBndr instTys) cons
  where
    checkAllowed =
      case variant of
        Datatype        -> pure ()
        Newtype         -> pure ()
        DataInstance    -> dataFamilyError
        NewtypeInstance -> dataFamilyError
#if MIN_VERSION_th_abstraction(0,5,0)
        TH.Abs.TypeData -> fail "makeBaseFunctor: `type data` declarations are not supported."
#endif

    dataFamilyError = fail "makeBaseFunctor: Data families are currently not supported."

    toTyVarBndr :: Type -> TyVarBndrVis
    toTyVarBndr (VarT n)          = plainTV n
    toTyVarBndr (SigT (VarT n) k) = kindedTV n k
    toTyVarBndr _                 = error "toTyVarBndr"

makePrimForDI' :: BaseRules
               -> Maybe (Name -> [Dec] -> Dec) -- ^ make instance
               -> Bool -> Name
               -> [TyVarBndrVis]
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
            [conF] | isNewtype ->
                NewtypeD [] tyNameF varsF Nothing conF deriveds
            _ ->
                DataD [] tyNameF varsF Nothing consF deriveds
          where
            deriveds =
#if MIN_VERSION_template_haskell(2,12,0)
              [DerivClause derivStrat
                [ ConT functorTypeName
                , ConT foldableTypeName
                , ConT traversableTypeName ]]
#else
              [ ConT functorTypeName
              , ConT foldableTypeName
              , ConT traversableTypeName ]
#endif

    -- type instance Base
    baseDec <- tySynInstDCompat baseTypeName Nothing
                                [pure s] (pure $ conAppsT tyNameF vars')

    let mkInstance :: Name -> [Dec] -> Dec
        mkInstance = case mkInstance' of
            Just f  -> f
            Nothing -> \n ->
                InstanceD Nothing [] (ConT n `AppT` s)

    -- instance Fixed
    let fixedDec = mkInstance fixedTypeName [baseDec]

    -- instance Recursive
    projDec <- FunD projectValName <$> mkMorphism id (_baseRulesCon rules) cons'
    let recursiveDec = mkInstance recursiveTypeName [projDec]

    -- instance Corecursive
    embedDec <- FunD embedValName <$> mkMorphism (_baseRulesCon rules) id cons'
    let corecursiveDec = mkInstance corecursiveTypeName [embedDec]

    -- Combine
    A.pure [dataDec, fixedDec, recursiveDec, corecursiveDec]

-- | makes clauses to rename constructors
mkMorphism
    :: (Name -> Name)
    -> (Name -> Name)
    -> [ConstructorInfo]
    -> Q [Clause]
mkMorphism nFrom nTo args = for args $ \ci -> do
    let n = constructorName ci
    fs <- replicateM (length (constructorFields ci)) (newName "x")
    clause [conP (nFrom n) (map varP fs)]                            -- patterns
                 (normalB $ foldl appE (conE $ nTo n) (map varE fs)) -- body
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
    go (InfixT l n r)     = InfixT (go l) n (go r)
    go (UInfixT l n r)    = UInfixT (go l) n (go r)
    go (ParensT t)        = ParensT (go t)
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
-- TH-quoted names
-------------------------------------------------------------------------------
-- Note that this module only TemplateHaskellQuotes, not TemplateHaskell,
-- which makes lens able to be used in stage1 cross-compilers.

fixedTypeName :: Name
fixedTypeName = ''Fixed

baseTypeName :: Name
baseTypeName = ''Base

recursiveTypeName :: Name
recursiveTypeName = ''Recursive

corecursiveTypeName :: Name
corecursiveTypeName = ''Corecursive

projectValName :: Name
projectValName = 'project

embedValName :: Name
embedValName = 'embed

functorTypeName :: Name
functorTypeName = ''Functor

foldableTypeName :: Name
foldableTypeName = ''Foldable

traversableTypeName :: Name
traversableTypeName = ''Traversable
