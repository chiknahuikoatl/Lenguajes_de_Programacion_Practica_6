module BAE.Memory where

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

type Identifier = String
type Address = Int
type Value = Expr

type Cell = (Address, Value)
type Memory = [Cell]


newAddress :: Memory -> Expr
newAddress [] = L 0
newAddress m = (newAddressEncuentra (newAddressAux m) 0)

access :: Address -> Memory -> Maybe Value
access _ [] = Nothing
access k ((n,v):xs)
    | k == n = Just v
    | otherwise = (access k xs)

update :: Cell -> Memory -> Memory
update c [] = (insert [] c)
update (n1,v1) ((n2,v2):xs)
    | n1 == n2 = Just (n1,v1):xs
    | otherwise = ((n2,v2):(update (n1,v1) xs))

normal :: Expr -> bool
normal (V v) = True
normal (I n) = True
normal (B b) = True
normal (Fn _ e) = (normal e)
normal _ = False

insert :: Memory -> Cell -> Memory
insert ((n,v):xs) (m,w)
    | (n > m) = ((n,v):(insert xs (m,w)))
    | otherwise = ((m,w):((n,v):xs))

frVars :: Expr -> [Semantic.Identifier]
frVars Void = []
frVars (L n) = []
frVars (Alloc e) = (frVars e)
frVars (Deref e) = (frVars e)
frVars (Assig e1 e2) = (union (frVars e1) (frVars e2))
frVars (Seq e1 e2) = (union (frVars e1) (frVars e2))
frVars (While e1 e2) = (union (frVars e1) (frVars e2))

subst :: Expr -> Semantic.Substitution -> Expr
subst e subst (v, s) = case e of
    (V x) ->
        if (x == v) then s
        else (V x)
    Void -> Void
    (L n) -> (L n)
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
        if (lv == v) then error "Variable Error"
        else if (elem lv (frVars (s))) then error "Could not apply the substitution"
        else  Let lv (subst e1 sub) (subst e2 sub)
    (Fn lv e) ->
        if (lv == v) || (elem lv (frVars (s))) then (subst e sub)
        else (Fn lv (subst e sub))
    (App e1 e2) -> (App (subst e1 sub) (subst e2 sub))
    (Alloc e) -> (Alloc (subst e sub))
    (Deref e) -> (Deref (subst( e sub)))
    (Assig e1 e2) -> (Assig (subst e1 sub) (subst e2 sub))
    (Seq e1 e2) -> (Seq (subst e1 sub) (subst e2 sub))
    (While e1 e2) -> (While (subst e1 sub) (subst e2 sub))

eval1 :: (Memory, Expr) -> (Memory, Expr)
eval1 (xs, (I n)) = (xs, (I n))
eval1 (xs, (L n)) = (xs, (L n))
eval1 (xs, (V v)) = (xs, (V v))
eval1 (xs, (B n)) = (xs, (B n))
eval1 (xs, Void) = (xs, Void)
eval1 (xs, (Add e1 e2))
    | (e1 == (I n)) && (e2 == (I m)) = (xs, (I (n + m)))
    | (e1 == (V _)) = error "Error a sumar"
    | (e2 == (V _)) = error "Error a sumar"
    | (e2 == (B _)) = error "Error a sumar"
    | (e1 == (Void)) = error "Error a sumar"
    | (e2 == (Void)) = error "Error a sumar"
    | (e1 == (L _)) = error "Error a sumar"
    | (e2 == (L _)) = error "Error a sumar"
    | (e1 == (I n)) = (xs2',(Add (I n) e2'))
    | otherwise = (xs1',(Add e1' e2))
        where
            (xs1',e1') = (eval1 (xs, e1))
            (xs2', e2') = (eval1 (xs, e2))
eval1 (xs, (Mul e1 e2))
    | (e1 == (I n)) && (e2 == (I m)) = (xs, (I (n * m)))
    | (e1 == (V _)) = error "Error al multiplicar"
    | (e1 == (B _)) = error "Error al multiplicar"
    | (e2 == (V _)) = error "Error al multiplicar"
    | (e2 == (B _)) = error "Error al multiplicar"
    | (e1 == (Void)) = error "Error al multiplicar"
    | (e2 == (Void)) = error "Error al multiplicar"
    | (e1 == (L _)) = error "Error al multiplicar"
    | (e2 == (L _)) = error "Error al multiplicar"
    | (e1 == (I n)) = (xs2',(Mul (I n) e2'))
    | otherwise = (xs1',(Mul e1' e2))
        where
            (xs1',e1') = (eval1 (xs, e1))
            (xs2',e2') = (eval1 (xs, e2))
eval1 (xs, (Succ e))
    | (e == (I n)) = (xs, (I (n + 1)))
    | (e == (V _)) = error "Error a ejecutar Succ"
    | (e == (B _)) = error "Error a ejecutar Succ"
    | (e == (Void)) = error "Error a ejecutar Succ"
    | (e == (L _)) = error "Error a ejecutar Succ"
    | otherwise = (xs', (Succ e')) where (xs', e1') = (eval1 (xs, e))
eval1 (xs, (Pred e))
    | (e == (I n)) = (xs, (I (n + 1)))
    | (e == (V _)) = error "Error a ejecutar Pred"
    | (e == (B _)) = error "Error a ejecutar Pred"
    | (e == (Void)) = error "Error a ejecutar Pred"
    | (e == (L _)) = error "Error a ejecutar Pred"
    | otherwise = (xs', (Pred e')) where (xs', e1') = (eval1 (xs, e))
eval1 (xs, (Not e))
    | (e == (B True)) = (B False)
    | (e == (B False)) = (B True)
    | (e == (V _)) = error "Error a ejecutar Not"
    | (e == (I _)) = error "Error a ejecutar Not"
    | (e == (Void)) = error "Error a ejecutar Not"
    | (e == (L _)) = error "Error a ejecutar Not"
    | otherwise = (xs', (Not e')) where (xs', e1') = (eval1 (xs, e))
eval1 (xs, (And e1 e2))
    | (e1 == (B n)) && (e2 == (B m)) = (xs, (B (n && m)))
    | (e1 == (V _)) = error "Error a ejecutar And"
    | (e1 == (I _)) = error "Error a ejecutar And"
    | (e2 == (V _)) = error "Error a ejecutar And"
    | (e2 == (I _)) = error "Error a ejecutar And"
    | (e1 == (Void)) = error "Error a ejecutar And"
    | (e2 == (Void)) = error "Error a ejecutar And"
    | (e1 == (L _)) = error "Error a ejecutar And"
    | (e2 == (L _)) = error "Error a ejecutar And"
    | (e1 == (B n)) = (xs2', (And e1 e2'))
    | otherwise = (xs1', (And e1' e2))
        where
                (xs1', e1') = (eval1 (xs, e1))
                (xs2', e2') = (eval1 (xs, e2))
eval1 (xs, (Or e1 e2))
    | (e1 == (B n)) && (e2 == (B m)) = (xs, (B (n || m)))
    | (e1 == (V _)) = error "Error a ejecutar Or"
    | (e1 == (I _)) = error "Error a ejecutar Or"
    | (e2 == (V _)) = error "Error a ejecutar Or"
    | (e2 == (I _)) = error "Error a ejecutar Or"
    | (e1 == (Void)) = error "Error a ejecutar Or"
    | (e2 == (Void)) = error "Error a ejecutar Or"
    | (e1 == (L _)) = error "Error a ejecutar Or"
    | (e2 == (L _)) = error "Error a ejecutar Or"
    | (e1 == (B n)) = (xs2', (Or e1 e2'))
    | otherwise = (xs1', (Or e1' e2))
        where
            (xs1', e1') = (eval1 (xs, e1))
            (xs2', e2') = (eval1 (xs, e2))s
eval1 (xs, (Lt e1 e2))
    | (e1 == (I n)) && (e2 == (I m)) = (xs, (B (n < m)))
    | (e1 == (V _)) = error "Error a ejecutar Lt"
    | (e1 == (I _)) = error "Error a ejecutar Lt"
    | (e2 == (V _)) = error "Error a ejecutar Lt"
    | (e2 == (I _)) = error "Error a ejecutar Lt"
    | (e1 == (Void)) = error "Error a ejecutar Lt"
    | (e2 == (Void)) = error "Error a ejecutar Lt"
    | (e1 == (L _)) = error "Error a ejecutar Lt"
    | (e2 == (L _)) = error "Error a ejecutar Lt"
    | (e1 == (I n)) = (xs2', (Lt e1 e2'))
    | otherwise = (xs1', (Lt e1' e2))
        where
            (xs1', e1') = (eval1 (xs, e1))
            (xs2', e2') = (eval1 (xs, e2))
eval1 (xs, (Gt e1 e2))
    | (e1 == (I n)) && (e2 == (I m)) = (xs, (B (n > m)))
    | (e1 == (V _)) = error "Error a ejecutar Gt"
    | (e1 == (I _)) = error "Error a ejecutar Gt"
    | (e2 == (V _)) = error "Error a ejecutar Gt"
    | (e2 == (I _)) = error "Error a ejecutar Gt"
    | (e1 == (Void)) = error "Error a ejecutar Gt"
    | (e2 == (Void)) = error "Error a ejecutar Gt"
    | (e1 == (L _)) = error "Error a ejecutar Gt"
    | (e2 == (L _)) = error "Error a ejecutar Gt"
    | (e1 == (I n)) = (xs2', (Gt e1 e2'))
    | otherwise = (xs1', (Gt e1' e2))
        where
            (xs1', e1') = (eval1 (xs, e1))
            (xs2', e2') = (eval1 (xs, e2))
eval1 (xs, (Eq e1 e2))
    | (e1 == (I n)) && (e2 == (I m)) = (xs, (B (n == m)))
    | (e1 == (V _)) = error "Error a ejecutar Eq"
    | (e1 == (I _)) = error "Error a ejecutar Eq"
    | (e2 == (V _)) = error "Error a ejecutar Eq"
    | (e2 == (I _)) = error "Error a ejecutar Eq"
    | (e1 == (Void)) = error "Error a ejecutar Eq"
    | (e2 == (Void)) = error "Error a ejecutar Eq"
    | (e1 == (L _)) = error "Error a ejecutar Eq"
    | (e2 == (L _)) = error "Error a ejecutar Eq"
    | (e1 == (I n)) = (xs2', (Eq e1 e2'))
    | otherwise = (xs1', (Eq e1' e2))
          where
              (xs1', e1') = (eval1 (xs, e1))
              (xs2', e2') = (eval1 (xs, e2))
eval1 (xs, (If e1 e2 e3))
    | (e1 == (B True)) = (xs, e2)
    | (e1 == (B False)) = (xs, e3)
    | (e1 == (I _)) = error "Error a ejecutar If"
    | (e1 == (V _)) = error "Error a ejecutar If"
    | (e1 == (L _)) = error "Error a ejecutar If"
    | (e1 == Void) = error "Error a ejecutar If"
    | otherwise = (xs', (If e1' e2 e3))
          where (xs', e1') = (eval1 (xs, e1))
eval1 (xs, (Let v e1 e2))
    | (e1 == Void) = error "Error a ejecutar Let"
    | (v != (V _)) = error "Error a ejecutar Let"
    | (e1 == (I _)) = (xs, (subst e2 (v, e1)))
    | (e1 == (B _)) = (xs, (subst e2 (v, e1)))
    | (e1 == (V _)) = (xs, (subst e2 (v, e1)))
    | (e1 == (L _)) = (xs, (subst e2 (v, e1)))
    | otherwise = (xs', (Let v e1 e2'))
          where (xs', e1') = (eval1 (xs, e1))
eval1 (xs, (App e1 e2))
    | ((normal e1) == False) = (xs1', (App e1' e2))
    | ((normal e2) == False) = (xs2', (App e1 e2'))
    | (e1 == (Fn v e1)) = (xs, (subst e1 (v, e2)))
    | otherwise = "normal e2 Necesita una función para App"
          where
            (xs1',e1') = (eval (xs,e1))
            (xs2',e2') = (eval (xs,e2))
eval1 (xs, (Alloc e))
    | (e == (I n))  = ((insert xs (m,e)), (L m))
    | (e == (Bool n))  = ((insert xs (m,e)), (L m))
    | (e == (Fn f n)) = ((insert xs (m,e)), (L m))
    | (e == (L _)) = error "Error a hacer Alloc"
    | (e == Void) = error "Error a hacer Alloc"
    | otherwise = (xs', (Alloc e'))
        where
            (xs',e') = (eval1 (xs, e))
            m = (newAddress xs)
eval1 (xs, (Deref e))
    | (e == (L n)) = (xs, (access n xs))
    | (e == (V _)) = error "Error a ejecutar Deref"
    | (e == (B _)) = error "Error a ejecutar Deref"
    | (e == (I _)) = error "Error a ejecutar Deref"
    | otherwise = (xs', (Deref e')) where (xs',e') = (eval1 (xs, e))
eval1 (xs, (Assig e1 e2))
    | (e1 == (L n)) && ((e2 == (V _)) || (e2 == (B _)) || (e2 == (I _))) = ((update (n,e2) xs), Void)
    | (e1 == (V _)) = error "Error a ejecutar Assig"
    | (e1 == (B _)) = error "Error a ejecutar Assig"
    | (e1 == (I _)) = error "Error a ejecutar Assig"
    | (e2 == Void) = error "Error a ejecutar Assig"
    | (e1 == (L n)) = (xs2', (Assig e1 e2'))
    | otherwise = (xs1', (Assig e1' e2))
        where
            (xs1',e1') = (eval1 (xs, e1))
            (xs2',e2') = (eval1 (xs, e2))
eval1 (xs, Void) = (xs, Void)
eval1 (xs, (Seq e1 e2))
    | (e1 == Void) = (xs, e2)
    | (!(normal e1)) = (xs', Seq e1' e2)
    | otherwise = error "e1 no válido para Seq"
        where (xs', e1') = (eval1 xs e1)
eval1 (xs, While e1 e2) = (xs, If e1 (While e1 e2) Void)

evals :: (Memory, Expr) -> (Memory, Expr)
evals (xs, (I n)) = (xs, (I n))
evals (xs, (B n)) = (xs, (B n))
evals (xs, (V v)) = (xs, (V v))
evals (xs, (L n)) = (xs, (L n))
evals (xs, Void) = (xs, Void)
evals (xs, (Add e1 e2)) = (evalsAux (xs'', (Add e1'  e2')))
    where
        (xs',e1') = (evals (xs, e1))
        (xs'', e2') = (evals (xs', e2))
evals (xs, (Mul e1 e2)) = (evalsAux (xs'', (Mul e1'  e2')))
    where
        (xs',e1') = (evals (xs, e1))
        (xs'', e2') = (evals (xs', e2))
evals (xs, (Succ e))
    | (e == (I n)) = (xs, (I (n + 1)))
    | otherwise = (evalsAux (xs', (Succ e')))
        where (xs',e') = (evals (xs, e))
evals (xs, (Pred e)) = (evalsAux (xs', (Pred e'))) where (xs',e') = (evals (xs, e))
evals (xs, (Not e)) = (evalsAux (xs', (Pred e'))) where (xs',e') = (evals (xs, e))
evals (xs, (And e1 e2)) = (evalsAux (xs'', (And e1' e2')))
    where
        (xs',e1') = (evals (xs, e1))
        (xs'', e2') = (evals (xs', e2))
evals (xs, (Or e1 e2)) = (evalsAux (xs'', (Or e1' e2')))
    where
        (xs',e1') = (evals (xs, e1))
        (xs'', e2') = (evals (xs', e2))
evals (xs, (Lt e1 e2))  = (evalsAux (xs'', (Lt e1' e2')))
    where
        (xs',e1') = (evals (xs, e1))
        (xs'', e2') = (evals (xs', e2))
evals (xs, (Gt e1 e2)) = (evalsAux (xs'', (Gt e1' e2')))
    where
        (xs',e1') = (evals (xs, e1))
        (xs'', e2') = (evals (xs', e2))
evals (xs, (Eq e1 e2)) = (evalsAux (xs'', (Eq e1' e2')))
    where
        (xs',e1') = (evals (xs, e1))
        (xs'', e2') = (evals (xs', e2))
evals (xs, (If e1 e2 e3)) = (evalsAux (xs''', (If e1' e2' e3')))
    where
        (xs',e1') = (evals (xs, e1))
        (xs'', e2') = (evals (xs', e2))
        (xs''', e3') = (evals (xs'', e3))
evals (xs, (Let e1 e2 e3)) = (evalsAux (xs''', (Let e1' e2' e3')))
    where
        (xs',e1') = (evals (xs, e1))
        (xs'', e2') = (evals (xs', e2))
        (xs''', e3') = (evals (xs'', e3))
evals (xs, (App e1 e2)) = (evalsAux (xs'', (App e1' e2')))
    where
        (xs',e1') = (evals (xs, e1))
        (xs'', e2') = (evals (xs', e2))
evals (xs, (Alloc e)) = (evalsAux (xs', (Pred e')))
    where (xs',e') = (evals (xs, e))
evals (xs, (Deref e)) = (evalsAux (xs', (Pred e')))
    where (xs',e') = (evals (xs, e))
evals (xs, (Assig e1 e2)) = (evalsAux (xs'', (Assig e1' e2')))
    where
        (xs',e1') = (evals (xs, e1))
        (xs'', e2') = (evals (xs', e2))


evale :: (Memory, Expr) -> (Memory, Expr)
evale (xs, (I n)) = (xs, (I n))
evale (xs, (L n)) = (xs, (L n))
evale (xs, (V v)) = (xs, (V v))
evale (xs, (B n)) = (xs, (B n))
evale (xs, Void) = (xs, Void)
evale (xs, (Add e1 e2)) = (eval1 (xs'', (Add e1'  e2')))
    where
        (xs',e1') = (evale (xs, e1))
        (xs'', e2') = (evale (xs', e2))
evale (xs, (Mul e1 e2)) = (eval1 (xs'', (Mul e1'  e2')))
    where
        (xs',e1') = (evale (xs, e1))
        (xs'', e2') = (evale (xs', e2))
evale (xs, (Succ e))
    | (e == (I n)) = (xs, (I (n + 1)))
    | otherwise = (evalAux (xs', (Succ e')))
        where (xs',e') = (evale (xs, e))
evale (xs, (Pred e)) = (eval1 (xs', (Pred e')))
    where (xs',e') = (evale (xs, e))
evale (xs, (Not e)) = (eval1 (xs', (Pred e')))
    where (xs',e') = (evale (xs, e))
evale (xs, (And e1 e2)) = (eval1 (xs'', (And e1' e2')))
    where
        (xs',e1') = (evale (xs, e1))
        (xs'', e2') = (evale (xs', e2))
evale (xs, (Or e1 e2)) = (eval1 (xs'', (Or e1' e2')))
    where
        (xs',e1') = (evale (xs, e1))
        (xs'', e2') = (evale (xs', e2))
evale (xs, (Lt e1 e2))  = (eval1 (xs'', (Lt e1' e2')))
    where
        (xs',e1') = (evale (xs, e1))
        (xs'', e2') = (evale (xs', e2))
evale (xs, (Gt e1 e2)) = (eval1 (xs'', (Gt e1' e2')))
    where
        (xs',e1') = (evale (xs, e1))
        (xs'', e2') = (evale (xs', e2))
evale (xs, (Eq e1 e2)) = (eval1 (xs'', (Eq e1' e2')))
    where
        (xs',e1') = (evale (xs, e1))
        (xs'', e2') = (evale (xs', e2))
evale (xs, (If e1 e2 e3)) = (eval1 (xs''', (If e1' e2' e3')))
    where
        (xs',e1') = (evale (xs, e1))
        (xs'', e2') = (evale (xs', e2))
        (xs''', e3') = (evale (xs'', e3))
evale (xs, (Let e1 e2 e3)) = (eval1 (xs''', (Let e1' e2' e3')))
    where
        (xs',e1') = (evale (xs, e1))
        (xs'', e2') = (evale (xs', e2))
        (xs''', e3') = (evale (xs'', e3))
evale (xs, (App e1 e2)) = (eval1 (xs'', (App e1' e2')))
    where
        (xs',e1') = (evale (xs, e1))
        (xs'', e2') = (evale (xs', e2))
evale (xs, (Alloc e)) = (eval1 (xs', (Pred e')))
    where (xs',e') = (evale (xs, e))
evale (xs, (Deref e)) = (eval1 (xs', (Pred e')))
    where (xs',e') = (evale (xs, e))
evale (xs, (Assig e1 e2)) = (eval1 (xs'', (Assig e1' e2')))
    where
        (xs',e1') = (evale (xs, e1))
        (xs'', e2') = (evale (xs', e2))


newAddressAux :: Memory -> [Int]
newAddressAux [] = []
newAddressAux ((n,v):xs) = [n]++(newAddressAux xs)

newAddressEncuentra :: [Int] -> Int -> Expr
newAddressEncuentra l n
    | (elem n l) = (newAddressEncuentra l (n+1))
    | otherwise = (L n)

evalsAux :: (Memory, Expr) -> (Memory, Expr)
evalsAux (xs, (Add e1 e2))
    | (e1 == (I n)) && (e2 == (I m)) = (xs, (I (n + m)))
    | otherwise = (xs, (Add e1 e2))
evalsAux (xs, (Mul e1 e2))
    | (e1 == (I n)) && (e2 == (I m)) = (xs, (I (n * m)))
    | otherwise = (Mul e1 e2)
evalsAux (xs, (Succ e))
    | (e == (I n)) = (xs, (I (n + 1)))
    | otherwise = (evals (xs, (Succ e)))
evalsAux (xs, (Pred e))
    | (e == (I n)) = (xs, (I (n + 1)))
    | otherwise = (xs, (Pred e))
evalsAux (xs, (Not e))
    | (e == (B True)) = (B False)
    | (e == (B False)) = (B True)
    | otherwise =  (xs, (Not e))
evalsAux (xs, (And e1 e2))
    | (e1 == (B n)) && (e2 == (B m)) = (xs, (B (n && m)))
    | otherwise = (xs, (And e1 e2))
evalsAux (xs, (Or e1 e2))
    | (e1 == (B n)) && (e2 == (B m)) = (xs, (B (n || m)))
    | otherwise = (xs, (Or e1 e2))
evalsAux (xs, (Lt e1 e2))
    | (e1 == (I n)) && (e2 == (I m)) = (xs, (B (n < m)))
    | otherwise =  (xs, (Lt e1 e2))
evalsAux (xs, (Gt e1 e2))
    | (e1 == (I n)) && (e2 == (I m)) = (xs, (B (n > m)))
    | otherwise = (xs, (Gt e1 e2))
evalsAux (xs, (Eq e1 e2))
    | (e1 == (I n)) && (e2 == (I m)) = (xs, (B (n == m)))
    | otherwise = (xs, (Eq e1 e2))
evalsAux (xs, (If e1 e2 e3))
    | (e1 == True) && ((e2 == (I _)) && (e3 == (I _)))  = e1
    | ((e2 == (B _)) && (e3 == (B _)))  = e1
    | ((e2 == (V _)) && (e3 == (V _)))  = e1
    | ((e2 == (L _)) && (e3 == (L _))) = e1
    | (e1 == False) && ((e2 == (I _)) && (e3 == (I _)))  = e2
    | ((e2 == (B _)) && (e3 == (B _)))  = e2
    | ((e2 == (V _)) && (e3 == (V _)))  = e2
    | ((e2 == (L _)) && (e3 == (L _))) = e2
    | otherwise = (xs, (If e1 e2 e3))
evalsAux (xs, (Let v e1 e2))
    | ((e2 == (I _)) ||(e2 == (B _)) || (e2 == (V _))) = (xs, (subst e1 (v, e2)))
    | otherwise = (xs, (Let v e1 e2))
evalsAux (xs, (App e1 e2))
    | (normal e1 == False) = (xs1', (App e1' e2))
    | (normal e2 == False) = (xs2', (App e1 e2'))
    | (e1 == (Fn v e)) = (xs, (subst e (v, e2)))
    | otherwise = (xs, (App e1 e2))
        where
            (xs2',e2') = (eval (xs,e2))
            (xs1',e1') = (eval (xs,e1))
evalsAux (xs, (Assig (L n) e))
    | (normal e) = (insert xs (n, e))
    | otherwise = (evals (xs', Assig (L n) e'))
        where (xs', e') = (eval1 (xs, e'))
evalsAux (xs, (Assig d e)) = (evals (xs', (Assig d' e)))
    where (xs', d') = (eval1 (xs, d))
-- evalsAux (xs, (Deref (L n)))
--     | v == Nothing = error "Memoria vacia."
--     | otherwise = (xs, v)
--         where v = (access n xs)
evalsAux (xs, (Deref e)) = (xs, (Deref e))
evalsAux (xs, (Assig (L n) (V v))) = ((update (n,(V v)) xs), Void)
evalsAux (xs, (Assig (L n) (B b))) = ((update (n,(B b)) xs), Void)
evalsAux (xs, (Assig (L n) (I i))) = ((update (n,(I i)) xs), Void)
evalsAux (xs, (Assig e1 e2)) = (xs, (Assig e1 e2))
