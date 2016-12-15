{-# LANGUAGE TypeFamilies #-}

module StgCse (stgCse) where

import DataCon
import Id
import StgSyn
import Outputable
import VarEnv
import CoreSyn (AltCon(..))
import Data.List (mapAccumL)
import TrieMap
import NameEnv
import Control.Monad( (>=>) )

-- A lookup trie

data StgArgMap a = SAM
    { sam_var :: DVarEnv a
    , sam_lit :: LiteralMap a
    }

instance TrieMap StgArgMap where
    type Key StgArgMap = StgArg
    emptyTM  = SAM { sam_var = emptyTM
                   , sam_lit = emptyTM }
    lookupTM (StgVarArg var) = sam_var >.> lkDFreeVar var
    lookupTM (StgLitArg lit) = sam_lit >.> lookupTM lit
    alterTM  (StgVarArg var) f m = m { sam_var = sam_var m |> xtDFreeVar var f }
    alterTM  (StgLitArg lit) f m = m { sam_lit = sam_lit m |> alterTM lit f }
    foldTM k m = foldTM k (sam_var m) . foldTM k (sam_lit m)
    mapTM f (SAM {sam_var = varm, sam_lit = litm}) =
        SAM { sam_var = mapTM f varm, sam_lit = mapTM f litm }

newtype ConAppMap a = CAM { un_cam :: DNameEnv (ListMap StgArgMap a) }

instance TrieMap ConAppMap where
    type Key ConAppMap = (DataCon, [StgArg])
    emptyTM  = CAM emptyTM
    lookupTM (dataCon, args) = un_cam >.> lkDNamed dataCon >=> lookupTM args
    alterTM  (dataCon, args) f m =
        m { un_cam = un_cam m |> xtDNamed dataCon |>> alterTM args f }
    foldTM k = un_cam >.> foldTM (foldTM k)
    mapTM f  = un_cam >.> mapTM (mapTM f) >.> CAM

-- The CSE Env

type CseEnv =
    ( ConAppMap Id
    , IdEnv Id
    , InScopeSet -- Id's mentioned in the two fields above
    )

emptyEnv :: CseEnv
emptyEnv = (emptyTM, emptyVarEnv, emptyInScopeSet)

envLookup :: DataCon -> [StgArg] -> CseEnv -> Maybe Id
envLookup dataCon args (env, _, _) = lookupTM (dataCon, args) env

addEnv :: Id -> DataCon -> [StgArg] -> CseEnv -> CseEnv
-- addEnv _ _ _ env = env
-- do not bother with nullary data constructors, they are static anyways
addEnv _ _ [] env = env
addEnv bndr dataCon args (env, subst, in_scope)
    = (new_env, subst, new_in_scope)
  where
    new_env = insertTM (dataCon, args) bndr env
    new_in_scope = extendInScopeSetList in_scope $
        bndr : [ id | StgVarArg id <- args ]

-- We do not want to mess with with the list of free variables
-- of an StgClosure (for now), so do not CSE across Lambdas
forgetCse :: CseEnv -> CseEnv
forgetCse (_, subst, in_scope) = (emptyTM, subst, in_scope)

addSubst :: Id -> Id -> CseEnv -> CseEnv
addSubst from to (env, subst, in_scope)
    = ( env
      , extendVarEnv subst from to
      , in_scope `extendInScopeSet` from `extendInScopeSet` to)

substArgs :: CseEnv -> [StgArg] -> [StgArg]
substArgs env = map (substArg env)

substArg :: CseEnv -> StgArg -> StgArg
substArg env (StgVarArg from) = StgVarArg (substVar env from)
substArg _   (StgLitArg lit)  = StgLitArg lit

substVars :: CseEnv -> [Id] -> [Id]
substVars env = map (substVar env)

substVar :: CseEnv -> Id -> Id
substVar (_, subst, _) from
    | Just to <- lookupVarEnv subst from = to
    | otherwise                          = from

-- Entering binders (updating in-scope-set to handle shadowing)
-- (Cargo-culted from CoreSubst.hs)

substBndr :: CseEnv -> Id -> (CseEnv, Id)
substBndr env@(_, _, in_scope) old_id
  = (new_env, new_id)
  where
    new_id = uniqAway in_scope old_id
    no_change = new_id == old_id
    new_env | no_change = env
            | otherwise = addSubst old_id new_id env

substBndrs :: CseEnv -> [Var] -> (CseEnv, [Var])
substBndrs env bndrs = mapAccumL substBndr env bndrs

substPairs :: CseEnv -> [(Var, a)] -> (CseEnv, [(Var, a)])
substPairs env bndrs = mapAccumL go env bndrs
  where go env (id, x) = let (env', id') = substBndr env id
                         in (env', (id', x))

-- Main entry point

stgCse :: [StgBinding] -> [StgBinding]
stgCse binds = map stgCseTopLvl binds

-- Top level bindings. We do not care about these

stgCseTopLvl :: StgBinding -> StgBinding
stgCseTopLvl (StgNonRec bndr rhs)
    = StgNonRec bndr (stgCseTopLvlRhs rhs)
stgCseTopLvl (StgRec eqs)
    = StgRec [ (bndr, stgCseTopLvlRhs rhs) | (bndr, rhs) <- eqs ]

stgCseTopLvlRhs :: StgRhs -> StgRhs
stgCseTopLvlRhs (StgRhsClosure ccs info occs upd args body)
    = let body' = stgCseExpr emptyEnv body
      in  StgRhsClosure ccs info occs upd args body'
stgCseTopLvlRhs (StgRhsCon ccs dataCon args)
    = StgRhsCon ccs dataCon args

-- The actual AST traversal

stgCseExpr :: CseEnv -> StgExpr -> StgExpr
stgCseExpr env (StgApp fun args)
    = StgApp fun' args'
  where fun' = substVar env fun
        args' = substArgs env args
stgCseExpr _ (StgLit lit)
    = StgLit lit
stgCseExpr env (StgConApp dataCon args tys)
    | Just bndr' <- envLookup dataCon args' env
    = StgApp bndr' []
    | otherwise
    = StgConApp dataCon args' tys
  where args' = substArgs env args
stgCseExpr env (StgOpApp op args tys)
    = StgOpApp op args' tys
  where args' = substArgs env args
stgCseExpr _ (StgLam _ _)
    = pprPanic "stgCseExp" (text "StgLam")
stgCseExpr env (StgCase scrut bndr ty alts)
    = let scrut' = stgCseExpr env scrut
          (env', bndr') = substBndr env bndr
          alts' = map (stgCseAlt env' bndr') alts
      in StgCase scrut' bndr' ty alts'
stgCseExpr env (StgTick tick body)
    = let body' = stgCseExpr env body
      in StgTick tick body'

stgCseExpr env (StgLet binds body)
    = let (binds', env') = stgCseBind env binds
          body' = stgCseExpr env' body
      in mkStgLet StgLet binds' body'

stgCseExpr env (StgLetNoEscape binds body)
    = let (binds', env') = stgCseBind env binds
          body' = stgCseExpr env' body
      in mkStgLet StgLetNoEscape binds' body'

stgCseAlt :: CseEnv -> Id -> StgAlt -> StgAlt
stgCseAlt env case_bndr (DataAlt dataCon, args, rhs)
    = let (env1, args') = substBndrs env args
          env2 = addEnv case_bndr dataCon (map StgVarArg args') env1
          rhs' = stgCseExpr env2 rhs
      in (DataAlt dataCon, args', rhs')
stgCseAlt env _ (altCon, args, rhs)
    = let (env1, args') = substBndrs env args
          rhs' = stgCseExpr env1 rhs
      in (altCon, args', rhs')

stgCseBind :: CseEnv -> StgBinding -> (Maybe StgBinding, CseEnv)
stgCseBind env (StgNonRec b e)
    = let (env1, b1) = substBndr env b
      in case stgCseRhs env1 b1 e of
        (Nothing,      env2) -> (Nothing,                env2)
        (Just (b2,e'), env2) -> (Just (StgNonRec b2 e'), env2)
stgCseBind env (StgRec pairs)
    = let (env1, pairs1) = substPairs env pairs
      in case stgCsePairs env1 pairs1 of
        ([],     env2) -> (Nothing, env2)
        (pairs2, env2) -> (Just (StgRec pairs2), env2)

stgCsePairs :: CseEnv -> [(Id, StgRhs)] -> ([(Id, StgRhs)], CseEnv)
stgCsePairs env [] = ([], env)
stgCsePairs env0 ((b,e):pairs)
  = let (pairMB, env1) = stgCseRhs env0 b e
        (pairs', env2) = stgCsePairs env1 pairs
    in (pairMB `mbCons` pairs', env2)
  where
    mbCons = maybe id (:)

stgCseRhs :: CseEnv -> Id -> StgRhs -> (Maybe (Id, StgRhs), CseEnv)
stgCseRhs env bndr (StgRhsCon ccs dataCon args)
    | Just bndr' <- envLookup dataCon args' env
    = (Nothing, addSubst bndr bndr' env)
    | otherwise
    = let env' = addEnv bndr dataCon args' env
      in (Just (bndr, StgRhsCon ccs dataCon args'), env')
  where args' = substArgs env args
stgCseRhs env bndr (StgRhsClosure ccs info occs upd args body)
    = let (env1, args') = substBndrs env args
          env2 = forgetCse env1
          body' = stgCseExpr env2 body
      in (Just (bndr, StgRhsClosure ccs info occs' upd args' body'), env)
  where occs' = substVars env occs

-- Utilities

-- | This function short-cuts let-bindings that are now obsolete
mkStgLet :: (t2 -> t1 -> t1) -> Maybe t2 -> t1 -> t1
mkStgLet _      Nothing      body = body
mkStgLet stgLet (Just binds) body = stgLet binds body

