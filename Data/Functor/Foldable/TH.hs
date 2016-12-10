{-# LANGUAGE TemplateHaskell #-}
module Data.Functor.Foldable.TH
  ( makeBaseFunctor
  , makeBaseFunctorWith
  , BaseRules (..)
  , baseRules
  ) where

import Data.Bifunctor (first)
import Data.Functor.Foldable
import Language.Haskell.TH

-- | Build base functor with a sensible default configuration.
--
-- /e.g./
--
-- @
-- data Expr a
--     = Lit a
--     | Add (Expr a) (Expr a)
--     | Mul (Expr a) (Expr a)
--   deriving (Show)
-- @
--
-- will create
--
-- @
-- data ExprF a x
--     = LitF a
--     | Add x x
--     | Mul x x
--   deriving ('Functor', 'Foldable', 'Traversable')
--
-- type instance 'Base' (Expr a) = ExprF a
--
-- instance 'Recursive' (Expr a) where
--     'project' (Lit x)   = LitF x
--     'project' (Add x y) = AddF x y
--     'project' (Mul x y) = MulF x y
--
-- instance 'Corecursive' (Expr a) where
--     'embed' (LitF x)   = Lit x
--     'embed' (AddF x y) = Add x y
--     'embed' (MulF x y) = Mul x y
-- @
--
-- @
-- 'makeBaseFunctor' = 'makeBaseFunctorWith' 'baseRules'
-- @
--
-- /Notes:/
--
-- 'makeBaseFunctor' works only with ADTs. Existentials and GADTs aren't supported.
makeBaseFunctor :: Name -> DecsQ
makeBaseFunctor = makeBaseFunctorWith baseRules

-- | Build base functor with a custom configuration.
makeBaseFunctorWith :: BaseRules -> Name -> DecsQ
makeBaseFunctorWith rules name = reify name >>= f
  where
    f (TyConI dec) = makePrimForDec rules dec
    f _            = fail "makeBaseFunctor: Expected type constructor name"

-- | /TODO/: Add functions to rename
--
-- * type: @(++ \"F\")@
--
-- * type constructors: @(++ \"F\")@
--
-- * infix type constructors: ?
--
-- * fields: @(++ \"F\")@
--
-- * infix fields: ?
--
data BaseRules = BaseRules
    { _baseRulesType  :: Name -> Name
    , _baseRulesCon   :: Name -> Name
    , _baseRulesField :: Name -> Name
    }

baseRules :: BaseRules
baseRules = BaseRules
    { _baseRulesType  = toFName
    , _baseRulesCon   = toFName
    , _baseRulesField = toFName
    }

toFName :: Name -> Name
toFName name = mkName $ nameBase name ++ "F"

varBindName :: TyVarBndr -> Name
varBindName (PlainTV n)    = n
varBindName (KindedTV n _) = n

makePrimForDec :: BaseRules -> Dec -> DecsQ
makePrimForDec rules dec = case dec of
#if MIN_VERSION_template_haskell(2,11,0)
  DataD    _ tyName vars _ cons _ -> do
    makePrimForDec' rules tyName vars cons
#else
  DataD    _ tyName vars cons _ ->
    makePrimForDec' rules tyName vars cons
#endif
  _ -> fail "makeFieldOptics: Expected data type-constructor"

makePrimForDec' :: BaseRules -> Name -> [TyVarBndr] -> [Con] -> DecsQ
makePrimForDec' rules tyName vars cons = do
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
    let fieldConsF = map (toF s r) fieldCons

    -- TODO: transform 'cons' directly
    let consF = map makeCon fieldConsF

    -- Data definition
    let dataDec = DataD [] tyNameF varsF Nothing consF [ConT ''Functor, ConT ''Foldable, ConT ''Traversable]

    -- type instance Base
    let baseDec = TySynInstD ''Base (TySynEqn [s] $ conAppsT tyNameF vars')

    -- instance Recursive
    args <- (traverse . traverse . traverse) (\_ -> newName "x") fieldCons

    let projDec = FunD 'project (mkMorphism id toFName args)
    let recursiveDec = InstanceD Nothing [] (ConT ''Recursive `AppT` s) [projDec]

    -- instance Corecurive
    let embedDec = FunD 'embed (mkMorphism toFName id args)
    let corecursiveDec = InstanceD Nothing [] (ConT ''Corecursive `AppT` s) [embedDec]

    -- Combine
    pure [dataDec, baseDec, recursiveDec, corecursiveDec]
  where
    toF s r (n, fs) = (_baseRulesCon rules n, map (toF' s r) fs)
    toF' s r (n, t) = (fmap (_baseRulesField rules) n, substType s r t)

    makeCon (name, fs) = NormalC name (map (f . snd) fs)
      where
        f t = (Bang NoSourceUnpackedness NoSourceStrictness, t)

-- | makes clauses to rename constructors
mkMorphism
    :: (Name -> Name)
    -> (Name -> Name)
    -> [(Name, [Name])]
    -> [Clause]
mkMorphism nFrom nTo args = flip map args $ \(n, fs) -> Clause
    [ConP (nFrom n) (map VarP fs)]     -- patterns
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

-- | Extraty type variables
typeVars :: [TyVarBndr] -> [Name]
typeVars = map varBindName

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
    go x | x == a = b
    go (VarT n) = VarT n
    go (AppT l r) = AppT (go l) (go r)
#if MIN_VERSION_template_haskell(2,11,0)
    go (ParensT t) = ParensT (go t)
#endif
    -- TODO:
    go x = x
