module Qlogic.Tseitin 
  (ExtendedAtom,
   transform,
   baseAssignment
  )
where
import qualified Control.Monad.State.Lazy as State
import qualified Data.Set as Set
import qualified Data.Map as Map
import Qlogic.Assign (Assign, toMap, fromMap, empty)
import Qlogic.Formula
import qualified Qlogic.Cnf as Cnf
import Qlogic.Cnf (CNF, (+&+), Literal(..))

data ExtendedAtom a = L (Formula a) -- ^ an atom representing a formula
                    | V a -- ^ an atom of the input formula
                      deriving (Eq, Ord, Show)

lit,nlit :: Formula a -> Literal (ExtendedAtom a)
lit (Var x) = PosLit $ V x
lit Top = TopLit
lit Bot = BotLit
lit (Neg x) = nlit x
lit fm      = Lit $ PosLit $ L fm

nlit :: Formula a -> ExtendedLiteral (ExtendedAtom a)
nlit fm = negate' $ lit fm
  where negate' (Lit (PosLit x)) = Lit (NegLit x)
        negate' (Lit (NegLit x)) = Lit (PosLit x)
        negate' TopLit           = BotLit
        negate' BotLit           = TopLit


toCnf :: Eq a => [[ExtendedLiteral a]] -> CNF a
toCnf = foldr appendClause Cnf.top
  where appendClause cl cnf | TopLit `elem` cl = cnf
                            | otherwise        = Cnf.singleton (Cnf.clause $ foldr lower [] cl) +&+ cnf
        lower BotLit l = l
        lower (Lit a) l = a:l

-- | The state monad for constructing CNFs exploits sharing by keeping
-- a record of so far translated subformulas
type PGSetMonad a r = State.State (St a) r

data St a = St { posSet :: Set.Set (Formula a) -- ^  lists all formulas with positive CNF constructed
               , negSet :: Set.Set (Formula a) -- ^ lists all formulas with negative CNF constructed
               }

getPSet :: PGSetMonad a (Set.Set (Formula a))
getNSet :: PGSetMonad a (Set.Set (Formula a))

getPSet = State.get >>= return . posSet
getNSet = State.get >>= return . negSet

setPSet :: Set.Set (Formula a) -> PGSetMonad a ()
setNSet :: Set.Set (Formula a) -> PGSetMonad a ()
setPSet set = State.modify $ \s -> s {posSet = set}
setNSet set = State.modify $ \s -> s {negSet = set}

maybeCompute_  :: Ord a => (PGSetMonad a (Set.Set (Formula a))) 
               -> (Set.Set (Formula a) -> PGSetMonad a ()) 
               -> Formula a 
               -> PGSetMonad a (CNF (ExtendedAtom a)) 
               -> PGSetMonad a (CNF (ExtendedAtom a))

maybeCompute_ getSet setSet fm m = 
  do s <- getSet
     case fm `Set.member` s of
       False -> setSet (Set.insert fm s) >> m
       True  -> return $ Cnf.top

maybeComputePos, maybeComputeNeg :: Ord a => Formula a -> PGSetMonad a (CNF (ExtendedAtom a)) -> PGSetMonad a (CNF (ExtendedAtom a))
maybeComputePos = maybeCompute_ getPSet setPSet
maybeComputeNeg = maybeCompute_ getNSet setNSet

transformPlus,transformMinus :: (Ord a) => (Formula a) -> PGSetMonad a (CNF (ExtendedAtom a))
transformPlus fm@(a `And` b) =
  maybeComputePos fm $
  do cnfA <- transformPlus a
     cnfB <- transformPlus b
     return $ toCnf [[nlit fm, lit a], [nlit fm, lit b]] +&+ cnfA +&+ cnfB
     -- bigAnd [(lvar fm) `Imp` (lvar a `And` lvar b), phiA, phiB]
transformPlus fm@(a `Or` b) =
  maybeComputePos fm $
  do cnfA <- transformPlus a
     cnfB <- transformPlus b
     return $ toCnf [[nlit fm, lit a, lit b]] +&+ cnfA +&+ cnfB
     -- bigAnd [(lvar fm) `Imp` (lvar a `Or` lvar b), phiA, phiB]
transformPlus fm@(a `Iff` b) =
  maybeComputePos fm $
  do cnfApos <- transformPlus a
     cnfAneg <- transformMinus a
     cnfBpos <- transformPlus b
     cnfBneg <- transformMinus b
     return $ toCnf [[nlit fm, nlit a, lit b], [nlit fm, lit a, nlit b]] +&+ cnfApos +&+ cnfBpos +&+ cnfAneg +&+ cnfBneg
     --  bigAnd [lvar fm `Imp` (lvar a `Iff` lvar b), cnfApos, cnfAneg, cnfBpos, cnfBneg]
     -- fm -> (a <-> b)
     -- -fm | ((-a | b) & (a | -b))
     -- (-fm | -a | b) & (-fm | a | -b)
     --
transformPlus fm@(a `Imp` b) =
  maybeComputePos fm $
  do cnfA <- transformMinus a
     cnfB <- transformPlus b
     return $ toCnf [[nlit fm, nlit a, lit b]] +&+ cnfA +&+ cnfB
     -- bigAnd [lvar fm `Imp` (lvar a `Imp` lvar b), cnfA, cnfB]
transformPlus fm@(Neg a)       = maybeComputePos fm $ transformMinus a
transformPlus fm@(Var _)       = maybeComputePos fm $ return Cnf.empty
transformPlus Top              = maybeComputePos Top $ return Cnf.empty
transformPlus Bot              = maybeComputePos Bot $ return Cnf.empty

transformMinus fm@(a `And` b) =
  maybeComputeNeg fm $
  do cnfA <- transformMinus a
     cnfB <- transformMinus b
     return $ toCnf [[nlit a, nlit b, lit fm]] +&+ cnfA +&+ cnfB
            -- bigAnd [(lvar a `And` lvar b) `Imp` (lvar fm), cnfA, cnfB]
transformMinus fm@(a `Or` b) =
  maybeComputeNeg fm $ 
  do cnfA <- transformMinus a
     cnfB <- transformMinus b
     return $ toCnf [[nlit a, lit fm], [nlit b, lit fm]] +&+ cnfA +&+ cnfB
     -- [(lvar a `Or` lvar b) `Imp` (lvar fm)  , cnfA, cnfB]
     -- -a & -b | fm === (-a | fm) & (-b | fm)
transformMinus fm@(a `Iff` b) =
  maybeComputeNeg fm $
  do cnfApos <- transformPlus a
     cnfAneg <- transformMinus a
     cnfBpos <- transformPlus b
     cnfBneg <- transformMinus b
     return $ toCnf [[lit fm, lit a, lit b], [lit fm, nlit a, nlit b]] +&+ cnfApos +&+ cnfBpos +&+ cnfAneg +&+ cnfBneg

transformMinus fm@(a `Imp` b) =
  maybeComputeNeg fm $
  do cnfA <- transformPlus a
     cnfB <- transformMinus b
     return $ toCnf [[lit fm, lit a], [lit fm, nlit b]] +&+ cnfA +&+ cnfB
-- bigAnd [lvar (lvar a `Imp` lvar b) `Imp` fm, cnfA, cnfB]

transformMinus fm@(Neg a)     = maybeComputeNeg fm $ transformPlus a
transformMinus fm@(Var _)     = maybeComputeNeg fm $ return Cnf.empty
transformMinus Top            = maybeComputeNeg Top $ return Cnf.empty
transformMinus Bot            = maybeComputeNeg Bot $ return Cnf.empty

transformList :: Ord a => [Formula a] -> PGSetMonad a (CNF (ExtendedAtom a))
transformList fms = (mapM transform_ fms)  >>= return . foldr (+&+) Cnf.top
  where transform_ fm = do cnf <- transformPlus fm
                           return $ toCnf [[lit fm]] +&+ cnf

transform :: Ord a => Formula a -> CNF (ExtendedAtom a)
transform fm = State.evalState (transformList $ splitAnd fm) St{posSet = Set.empty, negSet = Set.empty}
  where splitAnd (a `And` b) = splitAnd a ++ splitAnd b
        splitAnd fm'          = [fm']

-- size decreasing simplification
-- simplify :: Formula a -> Formula a
-- simplify ((Neg a) `Or` b) = a `Imp` b
-- simplify (a `Or` (Neg b)) = b `Imp` a
-- simplify (Neg  (Neg a))   = a
-- simplify (Neg  ((Neg a) `And` (Neg b)))   = a `Or` b
-- simplify (Neg  ((Neg a) `Or` (Neg b)))   = a `And` b
-- simplify _ = undefined  -- TODO finish

baseAssignment :: Ord a => Assign (ExtendedAtom a) -> Assign a
baseAssignment = fromMap . Map.foldWithKey f empty . toMap
  where f (V x) e = Map.insert x e 
        f _ _     = id
