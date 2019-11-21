module BAE.Memory2 where

import qualified Data.List as List
import qualified BAE.Semantic as Semantic

data Expr = V Semantic.Identifier | I Int | B Bool
          | Add Expr Expr | Mul Expr Expr
          | Succ Expr | Pred Expr
          | Not Expr | And Expr Expr | Or Expr Expr
          | Lt Expr Expr | Gt Expr Expr | Eq Expr Expr
          | If Expr Expr Expr
          | Let Semantic.Identifier Expr Expr
          | Fn Semantic.Identifier Expr
          | App Expr Expr
          | L Int
          | Alloc Expr
          | Deref Expr
          | Assig Expr Expr
          | Void
          | Seq Expr Expr
          | While Expr Expr deriving (Eq)

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
      -- | Alloc Expr
      -- | Deref Expr
      -- | Assig Expr Expr
      -- | Void
      -- | Seq Expr Expr
      -- | While Expr Expr

type Identifier = String
type Substitution = (Identifier, Expr)
type Address = Int
type Value = Expr
type Cell = (Address, Value)
type Memory = [Cell]

-- Función newAddress y sus auxiliares
newAddress :: Memory -> Expr
newAddress [] = L 0
newAddress m = newAddressAux m

newAddressAux :: Memory -> Expr
newAddressAux m
    | (not b) = a
    | otherwise = error "Corrupted Memory."
        where
            a = (newAddressEncuentra l 0)
            (b, l) = (memoriaCorrupta m)

newAddressEncuentra :: [Int] -> Int -> Expr
newAddressEncuentra l n
    | (elem n l) = (newAddressEncuentra l (n+1))
    | otherwise = (L n)

-- Función access
access :: Address -> Memory -> Maybe Value
access _ [] = Nothing
access k ((n,v):xs)
    | b = error "Corrupted Memory."
    | k == n = Just v
    | otherwise = (access k xs)
        where (b, _) = (memoriaCorrupta ((n,v):xs))

-- Función update y sus auxiliares.
update :: Cell -> Memory -> Maybe Memory
update c [] = Nothing
update (a, v) m
    | not (normal v) = error "Memory can only store values."
    | not (fst (memoriaCorrupta m)) = Just (updateAux (a, v) m)
    | otherwise = error "Corrupted memory."

updateAux :: Cell -> Memory -> Memory
updateAux c [] = []
updateAux (n1,v1) ((n2,v2):xs)
    | n1 == n2 = (n1,v1):xs
    | otherwise = ((n2,v2):(updateAux (n1,v1) xs))

-- Función frVars
frVars :: Expr -> [Semantic.Identifier]
frVars (V x) = [x]
frVars (I n) = []
frVars (B b) = []
frVars (Add e1 e2) = List.union (frVars e1) (frVars e2)
frVars (Mul e1 e2) = List.union (frVars e1) (frVars e2)
frVars (Succ n) = []
frVars (Pred n) = []
frVars (Not b) = []
frVars (And b1 b2) = List.union (frVars b1) (frVars b2)
frVars (Or e1 e2) = List.union (frVars e1) (frVars e2)
frVars (Lt e1 e2) = List.union (frVars e1) (frVars e2)
frVars (Gt e1 e2) = List.union (frVars e1) (frVars e2)
frVars (Eq e1 e2) = List.union (frVars e1) (frVars e2)
frVars (If e1 e2 e3) = (frVars e1) ++ (frVars e2) ++ (frVars e3)
frVars (Let v e1 e2) = List.union (frVars e1) (frVars e2) List.\\ [v]
frVars (Fn v e) = (frVars e) List.\\ [v]
frVars (App e1 e2) = (List.union (frVars e1) (frVars e2))
frVars Void = []
frVars (L n) = []
frVars (Alloc e) = (frVars e)
frVars (Deref e) = (frVars e)
frVars (Assig e1 e2) = (List.union (frVars e1) (frVars e2))
frVars (Seq e1 e2) = (List.union (frVars e1) (frVars e2))
frVars (While e1 e2) = (List.union (frVars e1) (frVars e2))

-- Función de substitución
subst :: Expr -> Substitution -> Expr
subst e sub@(v, s) = case e of
    (V x) -> if (x == v) then s else (V x)
    (I n) -> (I n)
    (B b) -> (B b)
    (Add e1 e2) -> Add (subst e1 sub) (subst e2 sub)
    (Mul e1 e2) -> Mul (subst e1 sub) (subst e2 sub)
    (Succ e) -> Succ (subst e sub)
    (Pred e) -> Pred (subst e sub)
    (Not b) -> Not (subst b sub)
    (And e1 e2) -> And (subst e1 sub) (subst e2 sub)
    (Or e1 e2) -> Or (subst e1 sub) (subst e2 sub)
    (Lt e1 e2) -> Lt (subst e1 sub) (subst e2 sub)
    (Gt e1 e2) -> Gt (subst e1 sub) (subst e2 sub)
    (Eq e1 e2) -> Eq (subst e1 sub) (subst e2 sub)
    (If e1 e2 e3) -> If (subst e1 sub) (subst e2 sub) (subst e3 sub)
    (Let lv e1 e2) ->
        if (lv == v) then error "Variable Error in Let"
        else if (elem lv (frVars (s))) then error "Could not apply the substitution"
        else  Let lv (subst e1 sub) (subst e2 sub)
    (Fn lv e) ->
        if (lv == v) || (List.elem lv (frVars s)) then (subst e sub)
        else (Fn lv (subst e sub))
    (App e1 e2) -> (App (subst e1 sub) (subst e2 sub))
    (Alloc e) -> (Alloc (subst e sub))
    (Deref e) -> (Deref (subst e sub))
    (Assig e1 e2) -> (Assig (subst e1 sub) (subst e2 sub))
    (Seq e1 e2) -> (Seq (subst e1 sub) (subst e2 sub))
    (While e1 e2) -> (While (subst e1 sub) (subst e2 sub))







-- Funciones auxiliares
memoriaCorrupta :: Memory -> (Bool, [Int])
memoriaCorrupta m
    |(length (List.nub(naa))) == (length naa) = (False, naa)
    | otherwise = error "Corrupted Memory."
        where
            naa = (listaEnteroMemoria m)

listaEnteroMemoria :: Memory -> [Int]
listaEnteroMemoria [] = []
listaEnteroMemoria ((n,v):xs) = [n]++(listaEnteroMemoria xs)

normal :: Expr -> Bool
normal (V _) = True
normal (I _) = True
normal (B _) = True
normal (L _) = True
normal Void = True
normal (Fn _ e) = (normal e)
normal _ = False

-- No ha sido utilizada
insert :: Memory -> Cell -> Memory
insert [] c = [c]
insert ((n,v):xs) (m,w)
    | (not (normal w)) = error "Memory can only store values."
    | (n > m) = ((n,v):(insert xs (m,w)))
    | otherwise = ((m,w):((n,v):xs))
