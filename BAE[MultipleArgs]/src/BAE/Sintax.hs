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

data Frame = FnF Identifier Pending
           | AddFL Pending Expr
           | AddFR Expr Pending
           | MulFL Pending Expr
           | MulFR Expr Pending
           | SuccF Pending
           | PredF Pending
           | NotF Pending
           | AndFL Pending Expr
           | AndFR Expr Pending
           | OrFL Pending Expr
           | OrFR Expr Pending
           | LtFL Pending Expr
           | LtFR Expr Pending
           | GtFL Pending Expr
           | GtFR Expr Pending
           | EqFL Pending Expr
           | EqFR Expr Pending
           | IfF Pending Expr Expr
           -- | Let
           -- | Fn
           | AppFL Pending Expr
           | AppFR Expr Pending
           | AllocF Pending
           | DerefF Pending
           | AssigFL Pending Expr
           | AssigFR Expr Pending
           | SeqFL Pending Expr
           | SeqFR Expr Pending
           | WhileFL Pending Expr
           | WhileFR Expr Pending deriving (Eq)

instance Show Frame where
    show e = case e of
        (AddFL p e2) -> "Sum(-, " ++ (show e2) ++ ")"
        (AddFR e1 p) -> "Sum(" ++ (show e1) ++"-)"
        (MulFL p e2) -> "Mul(-, " ++ (show e2) ++ ")"
        (MulFR e1 p) -> "Mul(" ++ (show e1) ++"-)"
        (Succ n) -> "Succ(-)"
        (Pred n) -> "Pred(-)"
        (Not e) -> "Not(-)"
        (AndFL p e2) -> "And(-, " ++ (show e2) ++ ")"
        (AndFR e1 p) -> "And(" ++ (show e1) ++"-)"
        (OrFL p e2) -> "Or(-, " ++ (show e2) ++ ")"
        (OrFR e1 p) -> "Or(" ++ (show e1) ++"-)"
        (LtFL p e2) -> "Lt(-, " ++ (show e2) ++ ")"
        (LtFR e1 p) -> "Lt(" ++ (show e1) ++"-)"
        (GtFL p e2) -> "Gt(-, " ++ (show e2) ++ ")"
        (GtFR e1 p) -> "Gt(" ++ (show e1) ++"-)"
        (EqFL p e2) -> "Eq(-, " ++ (show e2) ++ ")"
        (EqFR e1 p) -> "Eq(" ++ (show e1) ++"-)"
        (If e1 e2 e3) -> "If(-," ++ (show e2) ++ ", " ++ (show e3) ++ ")"
        (Let v e1 e2) -> "Let(" ++ (show e1) ++ ", " ++ (show v) ++ "." ++ (show e2) ++ ")"
        (Fn v e) -> "\\"++v++"->"++(show e)
        (AppFL p e2) -> "App(-, " ++ (show e2) ++ ")"
        (AppFR e1 p) -> "App(" ++ (show e1) ++"-)"
        (L n) -> "L "++ (show n)
        Void -> "Void"
        (Alloc n) -> "Alloc(-)"
        (Deref e) -> "Deref(-)"
        (AssigFL p e2) -> "Assig(-, " ++ (show e2) ++ ")"
        (AssigFR e1 p) -> "Assig(" ++ (show e1) ++"-)"
        (SeqFL p e2) -> "Seq(-, " ++ (show e2) ++ ")"
        (SeqFR e1 p) -> "Seq(" ++ (show e1) ++"-)"
        (WhileFL p e2) -> "While(-, " ++ (show e2) ++ ")"
        (WhileFR e1 p) -> "While(" ++ (show e1) ++"-)"


type Identifier = String
type Substitution = (Identifier, Expr)
type Address = Int
type Value = Expr
type Cell = (Address, Value)
type Memory = [Cell]

type Pending = ()
type Stack = [Frame]
-- instance Show Stack where
--     show s = case s of
--         [] -> ""
--         (k:ks) -> (show k)++", "++(show ks)

data State = E (Memory, Stack, Expr)
           | R (Memory, Stack, Expr)
           | P (Memory, Stack, Expr) deriving (Eq)

instance Show State where
    show s = case s of
        (E (m, [], e)) -> "[] > "++(show e)
        (E (m, s, e)) -> (show s)++" > "++(show e)
        (R (m, [], e)) -> "[] < "++(show e)
        (R (m, s, e)) -> (show s)++" < "++(show e)
        (P (m, [], e)) -> "[] <- "++(show e)
        (P (m, s, e)) -> (show s)++" <- "++(show e)



-- Function declaration

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
subst (Handle e1 v e2) (y, e)
    | y == v = (Handle e1 v e2)
    | otherwise = (Handle e1 y (subst e2 (y, e)))

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
alphaEq (Fn v e) (Fn u f) = (alphaEq e (subst f (u, v)))
alphaEq (App e1 e2) (App f1 f2) = (alphaEq e1 f1) && (alphaEq e2 f2)
alphaEq (L n) (L m) = m == n
alphaEq (Alloc e1) (Alloc e2) =  (alphaEq e1 e2)
alphaEq (Deref e1) (Deref e2) =  (alphaEq e1 e2)
alphaEq (Assig e1 e2) (Assig f1 f2) = (alphaEq e1 f1) && (alphaEq e2 f2)
alphaEq (Void) (Void) = True
alphaEq (Seq e1 e2) (Seq f1 f2) = (alphaEq e1 f1) && (alphaEq e2 f2)
alphaEq (While e1 e2) (While f1 f2) = (alphaEq e1 f1) && (alphaEq e2 f2)
alphaEq (LetCC v1 e1 e2) (LetCC v2 e3 e4) = auxAE (LetCC v1 e1 e2) (Let v2 e3 e4)
alphaEq (Continue e1 e2) (Continue f1 f2) = (alphaEq e1 f1) && (alphaEq e2 f2)
alphaEq (Cont (x:xs)) (Cont (y:ys)) = (y == x) && (alphaEq (Cont xs) (Cont ys))
alphaEq (Raise e1) (Raise e2) =  (alphaEq e1 e2)
alphaEq (Handle e1 v e2) (Handle f1 u f2) = auxAE (Handle e1 v e2) (Handle f1 u f2)



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

auxAE :: Expr -> Expr -> Bool
auxAE (Let v e1 e2) (Let u f1 f2)
    | v == u = (alphaEq e1 f1) && (alphaEq e2 f2)
    | otherwise = (auxAE (Let v e1 e2) (subst (Let u f1 f2) (u, v) ))
auxAE (LetCC v e) (LetCC u f) = (auxAE (LetCC v e) (subst (LetCC u e) (u, v)))
auxAE (Handle v e1 e2) (Handle u f1 f2)
    | v == u = (alphaEq e1 f1) && (alphaEq e2 f2)
    | otherwise = (auxAE (Handle v e1 e2) (subst (Handle u f1 f2) (u, v) ))
