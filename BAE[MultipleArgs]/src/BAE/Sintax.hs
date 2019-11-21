module BAE.Sintax where

import Data.List
import Data.Char

--Declaration of data types.
data Expr = V Identifier | I Int | B Bool
          | Add Expr Expr | Mul Expr Expr
          | Succ Expr | Pred Expr
          | Not Expr | And Expr Expr | Or Expr Expr
          | Lt Expr Expr | Gt Expr Expr | Eq Expr Expr
          | If Expr Expr Expr
          | Let Identifier Expr Expr
          | Fn Identifier Expr
          | App Expr Expr
          | L Int
          | Alloc Expr
          | Deref Expr
          | Assig Expr Expr
          | Void
          | Seq Expr Expr
          | While Expr Expr
          | LetCC Identifier Expr
          | Continue Expr Expr
          | Cont Stack
          | Raise Expr  --raise(e)
          | Handle Expr Identifier Expr deriving (Eq)

instance Show Expr where
    show e = case e of
        (V x) -> "V[" ++ x ++ "]"
        (I n) -> "I[" ++ (show n) ++ "]"
        (B b) -> "B[" ++ (show b) ++ "]"
        (Add e1 e2) -> "Sum(" ++ (show e1) ++ ", " ++ (show e2) ++ ")"
        (Mul e1 e2) -> "Prod(" ++ (show e1) ++ ", " ++ (show e2) ++ ")"
        (Succ n) -> "Succ(" ++ (show n) ++ ")"
        (Pred n) -> "Pred(" ++ (show n) ++ ")"
        (Not e) -> "Not(" ++ (show e) ++ ")"
        (And e1 e2) -> "And(" ++ (show e1) ++ ", " ++ (show e2) ++ ")"
        (Or e1 e2) -> "Or(" ++ (show e1) ++ ", " ++ (show e2) ++ ")"
        (Lt e1 e2) -> "Lt(" ++ (show e1) ++ ", " ++ (show e2) ++ ")"
        (Gt e1 e2) -> "Gt(" ++ (show e1) ++ ", " ++ (show e2) ++ ")"
        (Eq e1 e2) -> "Eq(" ++ (show e1) ++ ", " ++ (show e2) ++ ")"
        (If e1 e2 e3) -> "If(" ++ (show e1) ++ ", " ++ (show e2) ++ ", " ++ (show e3) ++ ")"
        (Let v e1 e2) -> "Let(" ++ (show e1) ++ ", " ++ (show v) ++ "." ++ (show e2) ++ ")"
        (Fn v e) -> "\\"++v++"->"++(show e)
        (App e1 e2) -> (show e1)++" "++(show e2)
        (L n) -> "L "++ (show n)
        Void -> "Void"
        (Alloc e) -> "Alloc" ++ (show e)
        (Deref e) -> "Deref" ++ (show e)
        (Assig e1 e2) -> "Assig(" ++ (show e1) ++ ", " ++ (show e2) ++ ")"
        (Seq e1 e2) -> "Seq(" ++ (show e1) ++ ", " ++ (show e2) ++ ")"
        (While e1 e2) -> "While(" ++ (show e1) ++ ", " ++ (show e2) ++ ")"
        (LetCC v e) -> "LetCC("++(show v)++"."++show(e)++")"
        (Continue e1 e2) -> "Continue("++show(e1)++", "++show(e2)++")"
        (Cont s) -> "Cont(["++show(s)++"])"
        (Raise e) -> "Raise("++show(e)++")"
        (Handle e1 v e2) -> "Handle("++show(e1)++", "++show(v)++"."++show(e2)++")"

data Instruction = I Int | B Bool
                 | ADD | AND | DIV | Eq
                 | EXEC | GET| Gt | Lt
                 | MUL | NOT | POP | REM | SEL | SUB | SWAP
                 | ES [Instruction] deriving (Show)

type Identifier = String
type Substitution = (Identifier, Expr)
type Address = Int
type Value = Expr
type Cell = (Address, Value)
type Memory = [Cell]

type Program = [Instruction]

type Stack = [Frame]
instance Show Stack where
    show s = case s of
        [] -> ""
        (k:ks) -> (show k)++", "++(show ks)

type State = E (Memory, Stack, Expr)
           | R (Memory, Stack, Expr)
           | P (Memory, Stack, Expr) deriving (Show)

instance Show State where
    show s = case s of
        (E (m, [], e)) -> "[] > "++(show e)
        (E (m, s, e)) -> (show s)++" > "++(show e)
        (R (m, [], e)) -> "[] < "++(show e)
        (R (m, s, e)) -> (show s)++" < "++(show e)
        (P (m, [], e)) -> "[] <- "++(show e)
        (P (m, s, e)) -> (show s)++" <- "++(show e)



-- Function declaration

arithOperation :: Instruction -> Instruction -> Instruction -> Instruction
arithOperation (I f) (I s) ADD = (I (f + s))
arithOperation (I f) (I s) SUB = (I (f - s))
arithOperation (I f) (I s) MUL = (I (f * s))
arithOperation _ (I 0) DIV = error "Divided by zero."
arithOperation (I f) (I s) DIV = (I (div f s))
arithOperation _ (I 0) REM = error "Divided by zero."
arithOperation (I f) (I s) REM = (I (mod f s))
arithOperation _ _ _ = error "Operation error"


bboolOperation :: Instruction -> Instruction -> Instruction -> Instruction
bboolOperation (B f) (B s) AND = (B (f && s))
bboolOperation _ _ AND = error "Both perands are not boolean"

uboolOperation :: Instruction -> Instruction -> Instruction
uboolOperation (B f) NOT = (B (not f))
uboolOperation _ NOT = error "Not a boolean operand."

relOperation :: Instruction -> Instruction -> Instruction -> Instruction
relOperation (I f) (I s) Eq = (B (f == s))
relOperation (I f) (I s) Lt = (B (f < s))
relOperation (I f) (I s) Gt = (B (f > s))
relOperation _ _ _ = error "relOperation: Invalid arguments."

-- Have to check if third operator in SEL is a bool
stackOperation :: Stack -> Instruction -> Stack
stackOperation xs (I n) = ((I n):xs)
stackOperation xs (B b) = ((B b):xs)
stackOperation [] _ = error "Empty stack error."
stackOperation (x:xs) POP = xs
stackOperation (x:[]) _ = error "Not enough elements on stack."
stackOperation (x:y:xs) SWAP = (y:x:xs)
stackOperation (x:y:[]) SEL = error "Not enough elements on stack."
stackOperation (x:y:(B b):xs) SEL
    | b == False = x:xs
    | otherwise = y:xs
stackOperation (x:y:_:xs) SEL = error "Third element in stack is not boolean."
stackOperation ((I n):xs) GET = ((auxiliarGet xs n):xs)
stackOperation (_:xs) GET = error "Invalid parameter for GET"

auxiliarGet :: Stack -> Int -> Instruction
auxiliarGet [] _  = error "Not enough elements in stack."
auxiliarGet (x:xs) 1 = x
auxiliarGet (x:xs) n = (auxiliarGet xs (n-1))

execOperation :: Program -> Stack  -> Instruction -> (Program, Stack)
execOperation p ((ES q):xs) EXEC = (q ++ p, xs)
execOperation p [] EXEC = error "Nothing to execute"
execOperation _ _ _ = error "Invalid operation"



executeProgram :: Program -> Stack -> Stack
executeProgram [] s = s
executeProgram ((I n):xs) s = (executeProgram xs (stackOperation s (I n)))
executeProgram ((B b):xs) s = (executeProgram xs (stackOperation s (B b)))
executeProgram ((ES i):xs) s = (executeProgram xs ((ES i):s))
executeProgram ((ADD):xs) ((I x):(I y):s) = (executeProgram xs ((arithOperation (I y) (I x) ADD):s))
executeProgram ((ADD):xs) _ = error "Invalid parameters"
executeProgram ((SUB):xs) ((I x):(I y):s) = (executeProgram xs ((arithOperation (I y) (I x) SUB):s))
executeProgram ((SUB):xs) _ = error "Invalid parameters"
executeProgram ((MUL):xs) ((I x):(I y):s) = (executeProgram xs ((arithOperation (I y) (I x) MUL):s))
executeProgram ((MUL):xs) _ = error "Invalid parameters"
executeProgram ((DIV):xs) ((I x):(I y):s) = (executeProgram xs ((arithOperation (I y) (I x) DIV):s))
executeProgram ((DIV):xs) _ = error "Invalid parameters"
executeProgram ((REM):xs) ((I x):(I y):s) = (executeProgram xs ((arithOperation (I y) (I x) REM):s))
executeProgram ((REM):xs) _ = error "Invalid parameters"
executeProgram ((AND):xs) ((B f):(B t):s) = (executeProgram xs ((bboolOperation (B f) (B t) AND):s))
executeProgram ((AND):_) _ = error "Parámetros inválidos"
executeProgram ((NOT):xs) ((B f):s) = (executeProgram xs ((uboolOperation (B f) NOT):s))
executeProgram ((NOT):_) _ = error "Not enough parameters"
executeProgram ((Eq):xs) ((I x):(I y):s) = (executeProgram xs ((relOperation (I y) (I x) Eq):s))
executeProgram ((Eq):xs) _ = error "Invalid parameters"
executeProgram ((Gt):xs) ((I x):(I y):s) = (executeProgram xs ((relOperation (I y) (I x) Gt):s))
executeProgram ((Gt):xs) _ = error "Invalid parameters"
executeProgram ((Lt):xs) ((I x):(I y):s) = (executeProgram xs ((relOperation (I y) (I x) Lt):s))
executeProgram ((Lt):xs) _ = error "Invalid parameters"
executeProgram ((GET):xs) s = (executeProgram xs (stackOperation s GET))
executeProgram ((SEL):xs) s = (executeProgram xs (stackOperation s SEL))
executeProgram ((SWAP):xs) s = (executeProgram xs (stackOperation s SWAP))
executeProgram ((POP):xs) s = (executeProgram xs (stackOperation s POP))
executeProgram ((EXEC):xs) s = (let (a,b) = (execOperation xs s EXEC) in executeProgram a b)
-- Falta resolver executeOperation
--executeProgram

--
compile :: Expr -> Program
compile (N n) = [(I n)]
compile T = [(B True)]
compile F = [(B False)]
compile (Succ e) = ((compile e) ++ [(I 1), ADD])
compile (Pred e) = ((compile e) ++ [(I 1), SUB])
compile (e1 :+ e2) = ((compile e1) ++ (compile e2) ++ [ADD])
compile (e1 :- e2) = ((compile e1) ++ (compile e2) ++ [SUB])
compile (e1 :* e2) = ((compile e1) ++ (compile e2) ++ [MUL])
compile (e1 :/ e2) = ((compile e1) ++ (compile e2) ++ [DIV])
compile (e1 :% e2) = ((compile e1) ++ (compile e2) ++ [REM])
compile (Max e1 e2) = ( (compile e1) ++ (compile e2) ++ [Gt] ++ (compile e1) ++ (compile e2) ++ [SEL])
compile (Min e1 e2) = ((compile e1) ++ (compile e2) ++ [Gt] ++ (compile e2) ++ (compile e1) ++ [SEL])
compile (Not e) = ((compile e) ++ [NOT])
compile (e1 :& e2) = ((compile e1) ++ (compile e2) ++ [AND])
compile (e1 :| e2) = (((compile e1) ++ [NOT]) ++ ((compile e2) ++ [NOT]) ++ [AND, NOT])
compile (e1 :> e2) = ((compile e1) ++ (compile e2) ++ [Gt])
compile (e1 :< e2) = ((compile e1) ++ (compile e2) ++ [Lt])
compile (e1 := e2) = ((compile e1) ++ (compile e2) ++ [Eq])
compile (Fact e) = (compile e) ++ [ES [(I 2), GET, (I 1), Lt,
                     (ES [POP, POP, (I 1)]),
                     (ES [(I 2), GET, (I 1), SUB, (I 2), GET, (I 1), GET,
                         EXEC, SWAP, POP, MUL]),
                     SEL, EXEC],
                     (I 1), GET, EXEC]
compile (e1 :^ e2) = (compile e1) ++ (compile e2) ++
                [(ES [(I 2), GET, (I 1), Lt,
                    (ES [POP, POP, POP, (I 1)]),
                    (ES [SWAP, (I 1), SUB, (I 3), GET, SWAP, (I 3), GET,
                        (I 1), GET, EXEC, SWAP, POP, MUL]),
                    SEL, EXEC]),
                (I 1), GET, EXEC]

execute :: Expr -> Instruction
execute e
    | ((length (executeProgram (compile e) [])) > 1) = error "Stack finished with more than one element"
    | otherwise = (head (executeProgram (compile e) []))




frVars :: Expr -> [Identifier]
frVars (V i) = [i]
frVars (I n) = []
frVars (B b) = []
frVars (Add p s) = union (frVars p) (frVars s)
frVars (Mul p s) = union (frVars p) (frVars s)
frVars (Succ e) = (frVars e)
frVars (Pred e) = (frVars e)
frVars (Not e) = (frVars e)
frVars (And p s) = union (frVars p) (frVars s)
frVars (Or p s) = union (frVars p) (frVars s)
frVars (Lt p s) = union (frVars p) (frVars s)
frVars (Gt p s) = union (frVars p) (frVars s)
frVars (Eq p s) = union (frVars p) (frVars s)
frVars (If (B c) p s)
    | c == True = (frVars p)
    | otherwise = (frVars s)
frVars (Let i p s) = union (frVars p) ((frVars s) \\ [i])
frVars (Fn v e) = ((frVars e) \\ [v])
frVars (App e1 e2) = (union (frVars e1) (frVars e2))
frVars (L n) = []
frVars (Alloc e) = (frVars e)
frVars (Deref e) = (frvars e)
frVars (Assig e1 e2) = (union (frVars e1) (frVars e2))
frVars (Void) = []
frVars (Seq e1 e2) = (union (frVars e1) (frVars e2))
frVars (While e1 e2) = (union (frVars e1) (frVars e2))
frVars (LetCC v e) = (frVars e) \\ [v]
frVars (Continue e1 e2) = (union (frVars e1) (frVars e2))
frVars (Cont s) = []
frVars (Raise e) = (frvars e)
frVars (Handle e1 v e2) = union (frVars e1) ((frVars e2)\\[v])

subst :: Expr -> Substitution -> Expr
subst (I n) _ = (I n)
subst (B b) _ = (B b)
subst (V x) (y, e)
    | x == y = e
    | otherwise = (V x)
subst (Add e1 e2) s = (Add (subst e1 s) (subst e2 s))
subst (Mul e1 e2) s = (Mul (subst e1 s) (subst e2 s))
subst (Succ e1) s = (Succ (subst e1 s))
subst (Pred e1) s = (Pred (subst e1 s))
subst (Not e1) s = (Not (subst e1 s))
subst (And e1 e2) s = (And (subst e1 s) (subst e2 s))
subst (Or e1 e2) s = (Or (subst e1 s) (subst e2 s))
subst (Lt e1 e2) s = (Lt (subst e1 s) (subst e2 s))
subst (Gt e1 e2) s = (Gt (subst e1 s) (subst e2 s))
subst (Eq e1 e2) s = (Eq (subst e1 s) (subst e2 s))
subst (If c e1 e2) s = (If (subst c s) (subst e1 s) (subst e2 s))
subst (Let x e1 e2) (y, e)
    | (not (elem x (frVars e))) && (x == y) = (Let y (subst e1 (y, e)) (subst e2 (y, e)))
    | (not (elem x (frVars e))) && (x /= y) = (Let x (subst e1 (y, e)) (subst e2 (y, e)))
    | otherwise = error "Substitution not in free variables."
subst (Fn v e1) (y,e)
    | (not (elem v (frVars e))) && (v == y) = (Fn y (subst e1 (y, e)))
    | (not (elem x (frVars e))) && (x /= y) = (Fn x (subst e1 (y, e)))
    | otherwise = error "Substitution not in free variables."
subst (App e1 e2) (y, e)
    | (elem y (frVars e1)) && (elem y (frVars e2)) = (App (subst e1 (y, e)) (subst e2 (y, e)))
    | (elem y (frVars e1)) && (not (elem y (frVars e2))) = (App (subst e1 (y, e)) e2)
    | (elem y (frVars e2)) && (not (elem y (frVars e1))) = (App e1 (subst e2 (y, e)))
    | otherwise = error "Substitution not in free variables."
subst (LetCC v e) (y, f)
    | (not (elem v (frVars e))) && (v == y) = (LetCC y (subst e1 (y, e)))
    | (not (elem x (frVars e))) && (x /= y) = (LetCC x (subst e1 (y, e)))
    | otherwise = error "Substitution not in free variables."
subst (Continue e1 e2) s = (Continue (subst e1 s) (subst e2 s))
subst (Raise e) s = (Raise (subst e s))
subst (Handle e1 v e2) =

incrVar :: Identifier -> Identifier
incrVar v = (incrVarAux v)

alphaEq :: Expr -> Expr -> Bool
alphaEq (I n) (I m) = m == n
alphaEq (I n) _ = False
alphaEq (B b) (B c) = b == c
alphaEq (B b) _ = False
alphaEq (V x) (V y) = y == x
alphaEq (V x) _ = False
alphaEq (Add e1 e2) (Add e3 e4) = (alphaEq e1 e3) && (alphaEq e2 e4)
alphaEq (Add e1 e2) _ = False
alphaEq (Mul e1 e2) (Mul e3 e4) = (alphaEq e1 e3) && (alphaEq e2 e4)
alphaEq (Mul e1 e2) _ = False
alphaEq (Succ e1) (Succ e2) = (alphaEq e1 e2)
alphaEq (Succ e1) _ = False
alphaEq (Pred e1) (Pred e2) = (alphaEq e1 e2)
alphaEq (Pred e1) _ = False
alphaEq (Not e1) (Not e2) = (alphaEq e1 e2)
alphaEq (Not e1) _ = False
alphaEq (And e1 e2) (And e3 e4) = (alphaEq e1 e3) && (alphaEq e2 e4)
alphaEq (And e1 e2) _ = False
alphaEq (Or e1 e2) (Or e3 e4) = (alphaEq e1 e3) && (alphaEq e2 e4)
alphaEq (Or e1 e2) _ = False
alphaEq (Lt e1 e2) (Lt e3 e4) = (alphaEq e1 e3) && (alphaEq e2 e4)
alphaEq (Lt e1 e2) _ = False
alphaEq (Gt e1 e2) (Gt e3 e4) = (alphaEq e1 e3) && (alphaEq e2 e4)
alphaEq (Gt e1 e2) _ = False
alphaEq (Eq e1 e2) (Eq e3 e4) = (alphaEq e1 e3) && (alphaEq e2 e4)
alphaEq (Eq e1 e2) _ = False
alphaEq (If c1 e1 e2) (If c2 e3 e4) = (alphaEq c1 c2) && (alphaEq e1 e3) && (alphaEq e2 e4)
alphaEq (If c1 e1 e2) _ = False
alphaEq (Let v1 e1 e2) (Let v2 e3 e4)
    | auxAE (Let v1 e1 e2) (Let v2 e3 e4) = True
    | otherwise = False
alphaEq (Let v1 e1 e2) _ = False
alphaEq (Fn v e) (Fn u f) = (alphaEq e (subst f (u, v))
alphaEq (App e1 e2) (App f1 f2) = (alphaEq e1 f1) && (alphaEq e2 f2)
alphaEq (L n) (L m) = m == n
alphaEq (Alloc e1) (Alloc e2) =  (alphaEq e1 e2)
alphaEq (Deref e1) (Deref e2) =  (alphaEq e1 e2)
alphaEq (Assig e1 e2) (Assig f1 f2) = (alphaEq e1 f1) && (alphaEq e2 f2)
alphaEq (Void) (Void) = True
alphaEq (Seq e1 e2) (Seq f1 f2) = (alphaEq e1 f1) && (alphaEq e2 f2)
alphaEq (While e1 e2) (While f1 f2) = (alphaEq e1 f1) && (alphaEq e2 f2)
--LetCC
alphaEq (Continue e1 e2) (Continue f1 f2) = (alphaEq e1 f1) && (alphaEq e2 f2)
alphaEq (Raise e1) (Raise e2) =  (alphaEq e1 e2)
--HAndle



-- FUnciones auxiliares que incrementan el valor de la variable.

incrVarAux :: String -> String
incrVarAux s = (reverse (sacaString (reverse s))) ++ (show (strToInt (sacaInt (reverse s))))

sacaString :: String -> String
sacaString [] = []
sacaString (c:cs)
    | (isDigit c) = (sacaString cs)
    | otherwise = (c:cs)

sacaInt :: String -> String
sacaInt [] = []
sacaInt (c:cs)
    | (isDigit c) = [c] ++ (sacaInt cs)
    | otherwise = []
