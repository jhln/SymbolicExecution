module AbstractInterpretationSymbolicExecutionAndConstraints where

import qualified Data.Map as Map
import qualified Data.Set as Set

import Prelude hiding (seq)


-- type Var = Set.Set Int
-- type Val = Set.Set Values
data Var = Variable Int String deriving (Ord, Eq, Show)
data Val
  = Zero
  | One
  | N Int
  | C Char
  | S String
  | TopVal
--  | BottomVal

data Bottom = Bottom
data Top = Top

newtype Loc = Loc Int

type ConcreteState = Map.Map Var Val
concreteTrace :: (Var, Loc) -> Either Val (Either Bottom Top)
concreteTrace = undefined

type Arity = Int
--data Fun = Fun Var Arity [Param]
--data BFun = BFun Var Arity [Param]

data Exp
  = VarExp Var
  | ValExp Val
  | FuncExp Var Arity [Exp]
  | BoolExp BoolExp

data BoolExp
  = BZero
  | BOne
  | BFunc Var Arity [Exp]

data LSyntax
  = Skip String
  | Assign Var Exp
  | TopSyntax Var Top
  | Seq LSyntax LSyntax
  | Ite Loc BoolExp LSyntax LSyntax
  | While Loc BoolExp LSyntax

--- 3. Symbolic Execution

data Constraint
  = Cond BoolExp
  | NegCond BoolExp
  | CTop

type SymbolicState = Map.Map Var Exp 
data SymbolicTrace = ST [(Loc,Bool)] SymbolicState [Constraint]

extendedVarExpMap :: SymbolicState -> (Exp -> Exp)
extendedVarExpMap varToExp (VarExp x) = varToExp Map.! x
extendedVarExpMap varToExp (FuncExp fun arity params) 
  = FuncExp fun arity $ map (extendedVarExpMap varToExp) params
extendedVarExpMap varToExp (BoolExp (BFunc bFun arity params)) 
  = BoolExp $ BFunc bFun arity $ map (extendedVarExpMap varToExp) params
extendedVarExpMap _ c = c

initalState :: SymbolicTrace
initalState = ST [] Map.empty []


sos :: LSyntax -> SymbolicTrace -> SymbolicTrace
sos (Skip msg) state          = state
sos (Seq s1 s2) state   = sos s2 $ sos s1 state
sos (Assign x (ValExp TopVal)) (ST pi si phi) = ST pi si' phi
  where
    si' = Map.adjust (const $ (ValExp TopVal)) x si
sos (Assign x e) (ST pi si phi) = ST pi si' phi
  where
    si' = Map.adjust (const e) x si
sos (Ite loc b s1 s2) (ST pi si phi)
  | sat $ Cond b:phi    = 
      sos s1 $ ST (pi ++ [(loc, True)]) si $ Cond b:phi
  | otherwise           = 
      sos s2 $ ST (pi ++ [(loc, False)]) si $ NegCond b:phi
  where
    evalB = extendedVarExpMap si $ BoolExp b
sos (While loc b s) (ST pi si phi) 
  | sat $ Cond b:phi   = 
      sos 
        (Seq s $ While loc b s)
        $ ST (pi ++ [(loc, True)]) si $ Cond b:phi
  | otherwise     = ST (pi ++ [(loc, False)]) si $ NegCond b:phi
  where
    evalB = extendedVarExpMap si $ BoolExp b

sat :: [Constraint] -> Bool
sat = undefined

--- Example 1, Figure 2

assign :: String -> Int -> Exp -> LSyntax
assign name index value  = Assign (Variable index name) value

seq :: LSyntax -> LSyntax -> LSyntax
seq s1 s2 = Seq s1 s2

while :: Loc -> BoolExp -> LSyntax -> LSyntax
while loc b s = While loc b s

ite :: Loc -> BoolExp -> LSyntax -> LSyntax -> LSyntax
ite loc b s1 s2 = Ite loc b s1 s2

skip :: String -> LSyntax
skip = Skip 

exmaple1 :: LSyntax
exmaple1 = 
  seq (assign "x" 0 $ ValExp $ N 0)
    $ seq (assign "y" 1 $ ValExp TopVal)
      $ seq
        (while 
          (Loc 1)
          (BFunc 
            (Variable 2 ">") 
            2 
            [ VarExp (Variable 1 "y")
            , ValExp $ N 0])
          (seq 
              (assign "x" 0 $ 
                FuncExp 
                  (Variable 3 "plus") 
                  2 
                  [ VarExp $ Variable 0 "x"
                  , ValExp $ N 1])
              (assign "y" 1 $ 
                FuncExp 
                  (Variable 4 "minus") 
                  2 
                  [ VarExp $ Variable 1 "y"
                  , ValExp $ N 2])))
        $ ite 
            (Loc 2)
            (BFunc 
              (Variable 2 ">") 
              2 
              [ VarExp (Variable 0 "x")
              , ValExp $ N 1117])
            (Skip "StmtA")
            (Skip "StmtB")