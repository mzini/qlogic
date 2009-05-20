{-# LANGUAGE DeriveDataTypeable #-}

module Qlogic.Tseitin
where

import Control.Monad (liftM)
import qualified Control.Monad.State.Lazy as State
import qualified Data.Set as Set
import qualified Data.Map as Map
import Data.Typeable
import Qlogic.Assign (Assign, toMap, fromMap, empty)
import Qlogic.Formula hiding (fm)
import qualified Qlogic.Cnf as Cnf
import Qlogic.Cnf (CNF, (+&+), Literal(..), fromCnfs)

data ExtendedLiteral a = Lit !(Literal a)
                       | TopLit
                       | BotLit
                       deriving (Eq, Ord, Show)

data Form = Form PropositionalFormula deriving (Eq, Ord, Show, Typeable)
instance PropositionalAtomClass Form

isFormulaAtom :: PropositionalAtom -> Bool
isFormulaAtom a = case fromPropositionalAtom a of
                    Just (Form _) -> True
                    Nothing       -> False

lit :: PropositionalFormula -> ExtendedLiteral PropositionalAtom
lit (A x)   = Lit $ PosLit $ x
lit Top     = TopLit
lit Bot     = BotLit
lit (Neg x) = nlit x
lit fm      = Lit $ PosLit $ PropositionalAtom $ Form fm

nlit :: PropositionalFormula -> ExtendedLiteral PropositionalAtom
nlit fm = negate' $ lit fm
  where negate' (Lit (PosLit x)) = Lit (NegLit x)
        negate' (Lit (NegLit x)) = Lit (PosLit x)
        negate' TopLit           = BotLit
        negate' BotLit           = TopLit


toCnf :: Eq a => [[ExtendedLiteral a]] -> CNF a
toCnf = foldl appendClause Cnf.top
  where appendClause cnf cl | TopLit `elem` cl = cnf
                            | otherwise        = Cnf.singleton (Cnf.clause $ foldl lower [] cl) +&+ cnf
        lower l BotLit  = l
        lower l (Lit a) = a:l
        lower _ TopLit  = error "Tseitin.toCnf: Aggh. My head just exploded"

data St = St { posSet :: Set.Set PropositionalFormula -- ^ lists all formulas with positive CNF constructed
             , negSet :: Set.Set PropositionalFormula -- ^ lists all formulas with negative CNF constructed
             }

-- | The state monad for constructing CNFs exploits sharing by keeping
-- a record of so far translated subformulas
type PGSetMonad r = State.State St r


getPSet :: PGSetMonad (Set.Set PropositionalFormula)
getNSet :: PGSetMonad (Set.Set PropositionalFormula)

getPSet = liftM posSet State.get
getNSet = liftM negSet State.get

setPSet :: Set.Set PropositionalFormula -> PGSetMonad ()
setPSet set = State.modify $ \s -> s{posSet = set}

setNSet :: Set.Set PropositionalFormula -> PGSetMonad ()
setNSet set = State.modify $ \s -> s{negSet = set}

maybeCompute_  :: (PGSetMonad (Set.Set PropositionalFormula))
               -> (Set.Set PropositionalFormula -> PGSetMonad ())
               -> PropositionalFormula
               -> PGSetMonad (CNF PropositionalAtom)
               -> PGSetMonad (CNF PropositionalAtom)
maybeCompute_ getSet setSet fm m =
  do s <- getSet
     (if {-# SCC "tseitinSetLookup" #-} fm `Set.member` s
      then return Cnf.top
      else setSet (Set.insert fm s) >> m)

maybeComputePos, maybeComputeNeg :: PropositionalFormula -> PGSetMonad (CNF PropositionalAtom) -> PGSetMonad (CNF PropositionalAtom)
maybeComputePos = maybeCompute_ getPSet setPSet
maybeComputeNeg = maybeCompute_ getNSet setNSet

transformPlus,transformMinus :: PropositionalFormula -> PGSetMonad (CNF PropositionalAtom)
transformPlus fm@(And l) = {-# SCC "trposAnd" #-}
  maybeComputePos fm $
  do cnfs <- mapM transformPlus l
     return $ toCnf [[nlit fm, lit e] | e <- l] +&+ fromCnfs cnfs
transformPlus fm@(Or l) = {-# SCC "trposOr" #-}
  maybeComputePos fm $
  do cnfs <- mapM transformPlus l
     return $ toCnf [nlit fm : [lit e | e <- l]] +&+ fromCnfs cnfs
transformPlus fm@(a `Iff` b) = {-# SCC "trposIff" #-}
  maybeComputePos fm $
  do cnfApos <- transformPlus a
     cnfAneg <- transformMinus a
     cnfBpos <- transformPlus b
     cnfBneg <- transformMinus b
     return $ toCnf [[nlit fm, nlit a, lit b], [nlit fm, lit a, nlit b]] +&+ cnfApos +&+ cnfBpos +&+ cnfAneg +&+ cnfBneg
transformPlus fm@(Ite g t e) = {-# SCC "trposIte" #-}
  maybeComputePos fm $
  do cnfGpos <- transformPlus g
     cnfGneg <- transformMinus g
     cnfT <- transformPlus t
     cnfE <- transformPlus e
     return $ toCnf [[nlit fm, nlit g, lit t], [nlit fm, lit g, lit e]] +&+ cnfGpos +&+ cnfGneg +&+ cnfT +&+ cnfE

transformPlus fm@(a `Imp` b) = {-# SCC "trposImp" #-}
  maybeComputePos fm $
  do cnfA <- transformMinus a
     cnfB <- transformPlus b
     return $ toCnf [[nlit fm, nlit a, lit b]] +&+ cnfA +&+ cnfB
transformPlus fm@(Neg a)       = {-# SCC "trposNeg" #-} maybeComputePos fm $ transformMinus a
transformPlus fm@(A _)       = {-# SCC "trposAtom" #-} return Cnf.top
transformPlus Top              = {-# SCC "trposTop" #-} return Cnf.top
transformPlus Bot              = {-# SCC "trposBot" #-} return Cnf.top

transformMinus fm@(And l) = {-# SCC "trminAnd" #-}
  maybeComputeNeg fm $
  do cnfs <- mapM transformMinus l
     return $ toCnf [lit fm : [nlit e | e <- l]] +&+ fromCnfs cnfs
transformMinus fm@(Or l) = {-# SCC "trminOr" #-}
  maybeComputeNeg fm $ 
  do cnfs <- mapM transformMinus l
     return $ toCnf [[nlit e, lit fm] | e <- l] +&+ fromCnfs cnfs
transformMinus fm@(a `Iff` b) = {-# SCC "trminIff" #-}
  maybeComputeNeg fm $
  do cnfApos <- transformPlus a
     cnfAneg <- transformMinus a
     cnfBpos <- transformPlus b
     cnfBneg <- transformMinus b
     return $ toCnf [[lit fm, lit a, lit b], [lit fm, nlit a, nlit b]] +&+ cnfApos +&+ cnfBpos +&+ cnfAneg +&+ cnfBneg
transformMinus fm@(a `Imp` b) = {-# SCC "trminImp" #-}
  maybeComputeNeg fm $
  do cnfA <- transformPlus a
     cnfB <- transformMinus b
     return $ toCnf [[lit fm, lit a], [lit fm, nlit b]] +&+ cnfA +&+ cnfB
transformMinus fm@(Ite g t e) = {-# SCC "trminIte" #-}
  maybeComputeNeg fm $
  do cnfGpos <- transformPlus g
     cnfGneg <- transformMinus g
     cnfTneg <- transformMinus t
     cnfEneg <- transformMinus e
     return $ toCnf [[lit fm, nlit t, nlit g], [lit fm, nlit e, lit g]] +&+ cnfGpos +&+ cnfGneg +&+ cnfTneg +&+ cnfEneg
transformMinus fm@(Neg a)     = {-# SCC "trminNeg" #-} maybeComputeNeg fm $ transformPlus a
transformMinus fm@(A _)     = {-# SCC "trminAtom" #-} return Cnf.top
transformMinus Top            = {-# SCC "trminTop" #-} return Cnf.top
transformMinus Bot            = {-# SCC "trminBot" #-} return Cnf.top

transform :: PropositionalFormula -> CNF PropositionalAtom
transform fm = {-# SCC "Tseitin" #-} toCnf [[lit fm]] +&+ State.evalState (transformPlus fm) St{posSet = Set.empty, negSet = Set.empty}
