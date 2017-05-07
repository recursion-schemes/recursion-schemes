{-# LANGUAGE Rank2Types #-}
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
import Data.Traversable as T
import Data.Bifunctor (first)
import Data.Functor.Identity
import Language.Haskell.TH
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
--     'embed' (x :*$ y)  = x :*$ y
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
makeBaseFunctorWith rules name = reify name >>= f
  where
    f (TyConI dec) = makePrimForDec rules dec
    f _            = fail "makeBaseFunctor: Expected type constructor name"

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

makePrimForDec :: BaseRules -> Dec -> DecsQ
makePrimForDec rules dec = case dec of
#if MIN_VERSION_template_haskell(2,11,0)
  DataD    _ tyName vars _ cons _ ->
    makePrimForDec' rules False tyName vars cons
  NewtypeD _ tyName vars _ con _ ->
    makePrimForDec' rules True tyName vars [con]
#else
  DataD    _ tyName vars cons _ ->
    makePrimForDec' rules False tyName vars cons
  NewtypeD _ tyName vars con _ ->
    makePrimForDec' rules True tyName vars [con]
#endif
  _ -> fail "makeFieldOptics: Expected data type-constructor"

makePrimForDec' :: BaseRules -> Bool -> Name -> [TyVarBndr] -> [Con] -> DecsQ
makePrimForDec' rules isNewtype tyName vars cons = do
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
    let fieldCons = map normalizeConstructor cons

    let consF
          = conNameMap (_baseRulesCon rules)
          . conFieldNameMap (_baseRulesField rules)
          . conTypeMap (substType s r)
          <$> cons

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
#if MIN_VERSION_template_haskell(2,9,0)
    let baseDec = TySynInstD baseTypeName (TySynEqn [s] $ conAppsT tyNameF vars')
#else
    let baseDec = TySynInstD baseTypeName [s] $ conAppsT tyNameF vars'
#endif

    -- instance Recursive
    args <- (traverse . traverse . traverse) (\_ -> newName "x") fieldCons

    let projDec = FunD projectValName (mkMorphism id (_baseRulesCon rules) args)
#if MIN_VERSION_template_haskell(2,11,0)
    let recursiveDec = InstanceD Nothing [] (ConT recursiveTypeName `AppT` s) [projDec]
#else
    let recursiveDec = InstanceD [] (ConT recursiveTypeName `AppT` s) [projDec]
#endif

    -- instance Corecursive
    let embedDec = FunD embedValName (mkMorphism (_baseRulesCon rules) id args)
#if MIN_VERSION_template_haskell(2,11,0)
    let corecursiveDec = InstanceD Nothing [] (ConT corecursiveTypeName `AppT` s) [embedDec]
#else
    let corecursiveDec = InstanceD [] (ConT corecursiveTypeName `AppT` s) [embedDec]
#endif

    -- Combine
    pure [dataDec, baseDec, recursiveDec, corecursiveDec]

-- | makes clauses to rename constructors
mkMorphism
    :: (Name -> Name)
    -> (Name -> Name)
    -> [(Name, [Name])]
    -> [Clause]
mkMorphism nFrom nTo args = flip map args $ \(n, fs) -> Clause
    [ConP (nFrom n) (map VarP fs)]                      -- patterns
    (NormalB $ foldl AppE (ConE $ nTo n) (map VarE fs)) -- body
    [] -- where dec

-- | Normalized the Con type into a uniform positional representation,
-- eliminating the variance between records, infix constructors, and normal
-- constructors.
normalizeConstructor
  :: Con
  -> (Name, [(Maybe Name, Type)]) -- ^ constructor name, field name, field type

normalizeConstructor (RecC n xs) =
  (n, [ (Just fieldName, ty) | (fieldName,_,ty) <- xs])

normalizeConstructor (NormalC n xs) =
  (n, [ (Nothing, ty) | (_,ty) <- xs])

normalizeConstructor (InfixC (_,ty1) n (_,ty2)) =
  (n, [ (Nothing, ty1), (Nothing, ty2) ])

normalizeConstructor (ForallC _ _ con) =
  (fmap . fmap . first) (const Nothing) (normalizeConstructor con)

#if MIN_VERSION_template_haskell(2,11,0)
normalizeConstructor (GadtC ns xs _) =
  (head ns, [ (Nothing, ty) | (_,ty) <- xs])

normalizeConstructor (RecGadtC ns xs _) =
  (head ns, [ (Just fieldName, ty) | (fieldName,_,ty) <- xs])
#endif

-------------------------------------------------------------------------------
-- Traversals
-------------------------------------------------------------------------------

conNameTraversal :: Applicative f => (Name -> f Name) -> Con -> f Con
conNameTraversal f (NormalC n xs)       = NormalC <$> f n <*> A.pure xs
conNameTraversal f (RecC n xs)          = RecC <$> f n <*> pure xs
conNameTraversal f (InfixC l n r)       = InfixC l <$> f n <*> pure r
conNameTraversal f (ForallC xs ctx con) = ForallC xs ctx <$> conNameTraversal f con
#if MIN_VERSION_template_haskell(2,11,0)
conNameTraversal f (GadtC ns xs t)      = GadtC <$> T.traverse f ns <*> pure xs <*> pure t
conNameTraversal f (RecGadtC ns xs t)   = RecGadtC <$> traverse f ns <*> pure xs <*> pure t
#endif

conFieldNameTraversal :: Applicative f => (Name -> f Name) -> Con -> f Con
conFieldNameTraversal f (RecC n xs)          = RecC n <$> (traverse . tripleFst) f xs
conFieldNameTraversal f (ForallC xs ctx con) = ForallC xs ctx <$> conFieldNameTraversal f con
#if MIN_VERSION_template_haskell(2,11,0)
conFieldNameTraversal f (RecGadtC ns xs t)   = RecGadtC ns <$> (traverse . tripleFst) f xs <*> pure t
#endif
conFieldNameTraversal _ x = pure x

conTypeTraversal :: Applicative f => (Type -> f Type) -> Con -> f Con
conTypeTraversal f (NormalC n xs)       = NormalC n <$> (traverse . pairSnd) f xs
conTypeTraversal f (RecC n xs)          = RecC n <$> (traverse . tripleTrd) f xs
conTypeTraversal f (InfixC l n r)       = InfixC <$> pairSnd f l <*> pure n <*> pairSnd f r
conTypeTraversal f (ForallC xs ctx con) = ForallC xs ctx <$> conTypeTraversal f con
#if MIN_VERSION_template_haskell(2,11,0)
conTypeTraversal f (GadtC ns xs t)      = GadtC ns <$> (traverse . pairSnd) f xs <*> pure t
conTypeTraversal f (RecGadtC ns xs t)   = RecGadtC ns <$> (traverse . tripleTrd) f xs <*> pure t
#endif

conNameMap :: (Name -> Name) -> Con -> Con
conNameMap f = runIdentity . conNameTraversal (Identity . f)

conFieldNameMap :: (Name -> Name) -> Con -> Con
conFieldNameMap f = runIdentity . conFieldNameTraversal (Identity . f)

conTypeMap :: (Type -> Type) -> Con -> Con
conTypeMap f = runIdentity . conTypeTraversal (Identity . f)

-------------------------------------------------------------------------------
-- Monomorphic tuple lenses
-------------------------------------------------------------------------------

type Lens' s a = forall f. Functor f => (a -> f a) -> s -> f s

pairSnd :: Lens' (a, b) b
pairSnd f (a, b) = (,) a <$> f b

tripleTrd :: Lens' (a, b, c) c
tripleTrd f (a,b,c) = (,,) a b <$> f c

tripleFst :: Lens' (a, b, c) a
tripleFst f (a,b,c) = (\a' -> (a', b, c)) <$> f a

-------------------------------------------------------------------------------
-- Type mangling
-------------------------------------------------------------------------------

-- | Extraty type variables
typeVars :: [TyVarBndr] -> [Name]
typeVars = map varBindName

varBindName :: TyVarBndr -> Name
varBindName (PlainTV n)    = n
varBindName (KindedTV n _) = n

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
