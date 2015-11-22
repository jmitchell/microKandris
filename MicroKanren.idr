||| An implementation of MicroKanren according to
||| http://webyrd.net/scheme-2013/papers/HemannMuKanren2013.pdf
module MicroKanren

import Data.HVect

%default total

-- TODO: add tests

-- TODO: more features from the paper
--   - 4.2 infinite streams
--   - 4.3 interleaved streams
--   - 5 various user-level niceties
--   - 6 optimize lookups by using a persistent hash-table instead of assoc lists
--   - 6 consider preventing circular substitutions by adding occurs-check
--   - 6 reduce unnecessary inverse-eta-delays

data Var = MkVar Nat

instance Eq Var where
  (MkVar x) == (MkVar y) = x == y

varInjective : (MkVar n = MkVar m) -> n = m
varInjective Refl = Refl

instance DecEq Var where
  decEq (MkVar x) (MkVar y) with (decEq x y)
    decEq (MkVar x) (MkVar x) | Yes Refl = Yes Refl
    decEq (MkVar x) (MkVar y) | No contra = No $ \h : MkVar x = MkVar y => contra $ varInjective h

data StructuredData : Vect k Type -> Type where
  Nil : StructuredData []
  (::) : {t:Type} -> 
         {default %instance tEq : DecEq t} ->
         (v : t) ->
         StructuredData ts ->
         StructuredData (t::ts)

-- TODO: Make a type classes for converting from/to Idris types and
-- StructuredData. (See if it's feasible to create an instance for
-- arbitrary type providers.)

structuredDataInjective1 : {t:Type} -> {default %instance q : DecEq t} ->
               {x,y:t} -> (MicroKanren.(::) x xs = MicroKanren.(::) y ys) -> x = y
structuredDataInjective1 Refl = Refl

structuredDataInjective2 : {t:Type} -> {default %instance q : DecEq t} ->
               {x,y:t} -> (MicroKanren.(::) x xs = MicroKanren.(::) y ys) -> xs = ys
structuredDataInjective2 Refl = Refl

instance DecEq (StructuredData ts) where
  decEq [] [] = Yes Refl
  decEq ((::) {tEq=q} {ts=ts} x xs) ((::) {tEq=q} {ts=ts} y ys) with (decEq x y)
    decEq ((::) {tEq=q} {ts=ts} x xs) ((::) {tEq=q} {ts=ts} x ys) | Yes Refl with (decEq xs ys)
      decEq ((::) {tEq=q} {ts=ts} x xs) ((::) {tEq=q} {ts=ts} x xs) | Yes Refl | Yes Refl = Yes Refl
      decEq ((::) {tEq=q} {ts=ts} x xs) ((::) {tEq=q} {ts=ts} x ys) | Yes Refl | No contra = No $ \h => contra $ structuredDataInjective2 h
    decEq ((::) {tEq=q} {ts=ts} x xs) ((::) {tEq=q} {ts=ts} y ys) | No contra = No $ \h => contra $ structuredDataInjective1 h

data Term : Type where
  VarT : Var -> Term
  DatT : {ts : Vect k Type} -> StructuredData ts -> Term

data Subs = MkSubs (List (Var, Term))

varTermInjective : (VarT x = VarT y) -> x = y
varTermInjective Refl = Refl

varNotVect : (VarT x = DatT y) -> Void
varNotVect Refl impossible

emptyNotNonEmpty : {t:Type} -> {default %instance x : DecEq t} ->
                   {y:t} -> {ys:StructuredData ts} -> (DatT [] = DatT (y::ys)) -> Void
emptyNotNonEmpty Refl impossible

heqVecInjective1 : {t:Type} -> {default %instance x : DecEq t} ->
                   {x,y:t} -> (DatT (x::xs) = DatT (y::ys)) -> x = y
heqVecInjective1 Refl = Refl

heqVecInjective2 : {t:Type} -> {default %instance x : DecEq t} ->
                   {x,y:t} -> (DatT (x::xs) = DatT (y::ys)) -> xs = ys
heqVecInjective2 Refl = Refl

instance DecEq Term where
  decEq (VarT x) (VarT y) with (decEq x y)
    decEq (VarT x) (VarT x) | Yes Refl = Yes Refl
    decEq (VarT x) (VarT y) | No contra = No $ \h : VarT x = VarT y => contra $ varTermInjective h
  decEq (DatT []) (DatT []) = Yes Refl
  decEq (DatT []) (DatT (y::ys)) = No emptyNotNonEmpty
  decEq (DatT (x::xs)) (DatT []) = No $ negEqSym emptyNotNonEmpty
  -- TODO: Can any of this be cleaned up? It's nearly an exact
  -- duplicate of the DecEq StructuredData instance (which is also
  -- overwhelming).
  decEq (DatT ((::) {tEq=q} {ts=ts} x xs)) (DatT ((::) {tEq=q} {ts=ts} y ys)) with (decEq x y)
    decEq (DatT ((::) {tEq=q} {ts=ts} x xs)) (DatT ((::) {tEq=q} {ts=ts} x ys)) | Yes Refl with (decEq xs ys)
      decEq (DatT ((::) {tEq=q} {ts=ts} x xs)) (DatT ((::) {tEq=q} {ts=ts} x xs)) | Yes Refl | Yes Refl = Yes Refl
      decEq (DatT ((::) {tEq=q} {ts=ts} x xs)) (DatT ((::) {tEq=q} {ts=ts} x ys)) | Yes Refl | No contra = No $ \h => contra $ heqVecInjective2 h
    decEq (DatT ((::) {tEq=q} {ts=ts} x xs)) (DatT ((::) {tEq=q} {ts=ts} y ys)) | No contra = No $ \h => contra $ heqVecInjective1 h
  decEq (VarT x) (DatT y) = No varNotVect
  decEq (DatT x) (VarT y) = No $ negEqSym varNotVect

partial
walk : Term -> Subs -> Term
walk (VarT u) (MkSubs s) =
  case List.lookup u s of
    Just u' => walk u' (MkSubs s)
    Nothing => VarT u
walk u _ = u

extS : Var -> Term -> Subs -> Subs
extS x v (MkSubs s) = MkSubs ((x,v) :: s)

data State = MkState Subs Nat

data Stream = MkStream (List State)

data Goal = MkGoal (State -> Stream)

run : Goal -> State -> Stream
run (MkGoal f) sc = f sc

emptyState : State
emptyState = MkState (MkSubs []) 0

partial
unifySingletons : DecEq t => t -> t -> Subs -> Maybe Subs
unifySingletons u v s = case decEq u v of
  Yes _ => return s
  No _ => empty

partial
unify : Term -> Term -> Subs -> Maybe Subs
unify u v s = do
  case (walk u s, walk v s) of
    (VarT u', VarT v') => if u' == v'
                          then return s
                          else return $ extS u' (VarT v') s
    (VarT u', v') => return $ extS u' v' s
    (u', VarT v') => return $ extS v' u' s
    (DatT ((::) {tEq=q} u' []), DatT ((::) {tEq=q} v' [])) => unifySingletons u' v' s
    (DatT (u'::us'), DatT (v'::vs')) => do
      s' <- unify (DatT [u']) (DatT [v']) s
      s'' <- unify (DatT us') (DatT vs') s'
      return s''
    (u', v') => case decEq u' v' of
      Yes _ => return s
      No _ => empty

infixl 5 ===

partial
(===) : Term -> Term -> Goal
(===) u v = MkGoal (\(MkState s c) =>
  case unify u v s of
    Just s' => MkStream [MkState s' c]
    Nothing => MkStream [])

callFresh : (Var -> Goal) -> Goal
callFresh f = MkGoal (\(MkState s c) =>
  run (f (MkVar c))
                   (MkState s (c + 1)))

mplus : Stream -> Stream -> Stream
mplus (MkStream xs) (MkStream ys) = MkStream (xs ++ ys)

partial
bind : Stream -> Goal -> Stream
bind (MkStream []) g = MkStream []
bind (MkStream (x::xs)) g = mplus (run g x)
                                  (bind (MkStream xs) g)

disj : Goal -> Goal -> Goal
disj g1 g2 = MkGoal (\sc =>
  mplus (run g1 sc)
        (run g2 sc))

partial
conj : Goal -> Goal -> Goal
conj g1 g2 = MkGoal (\sc =>
  bind (run g1 sc) g2)


--------------------------------------------------

-- Examples


-- TODO: make Show instances to improve output readability.
-- TODO: consider implementing syntactic sugar to reduce verbosity.

partial
goalEx1 : Goal
goalEx1 = callFresh (\q => VarT q === DatT [5])

partial
ex1 : Stream
ex1 = run goalEx1 emptyState

partial
goalEx2 : Goal
goalEx2 = conj (callFresh (\a => VarT a === DatT [7]))
               (callFresh (\b => disj (VarT b === DatT [5])
                                      (VarT b === DatT [6])))

partial
ex2 : Stream
ex2 = run goalEx2 emptyState
