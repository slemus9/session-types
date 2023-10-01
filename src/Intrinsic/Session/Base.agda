{-# OPTIONS --guardedness #-}

open import Data.Bool.Base using (Bool)
open import Data.Fin.Base using (Fin)
open import Data.Integer.Base using (ℤ; _+_; -_)
open import Data.Nat.Base using (ℕ)
open import Data.Product using (_×_; _,_)
open import Data.Unit.Base using (⊤)
open import Function.Base using (_$_)
open import IO

-- Implementation from https://arxiv.org/abs/2303.01278
module Intrinsic.Session.Base where

-----------------
-- Definitions --
-----------------
data Sort : Set where
  int : Sort
  bool : Sort

-- Mapping from a Sort to its corresponding Type in agda:
T[_] : Sort -> Set
T[ int ] = ℤ
T[ bool ] = Bool

-- Binary Session:
data Session : Set

-- A session that depends on a set of labels modeled by Fin k:
Session[_] : (k : ℕ) -> Set
Session[ k ] = Fin k -> Session

data Session where
  !_∙_ : Sort -> Session -> Session
  ¿_∙_ : Sort -> Session -> Session
  ⨁ : ∀ {k} -> Session[ k ] -> Session -- internal choice
  & : ∀ {k} -> Session[ k ] -> Session -- external choice
  end : Session

{-
  Command: A representation of the application logic of a session, indexed by
  the type of the state of the application (A : Set) and by the Session it represents
-}
data Cmd (A : Set) : Session -> Set where
  send : ∀ {sort session}
    -> (A -> A × T[ sort ])
    -> Cmd A session
    -> Cmd A (! sort ∙ session)

  recv : ∀ {sort session}
    -> (T[ sort ] -> A -> A)
    -> Cmd A session
    -> Cmd A (¿ sort ∙ session)

  select : ∀ {k} {sessions : Session[ k ]}
    -> (i : Fin k)
    -> Cmd A (sessions i)
    -> Cmd A (⨁ sessions)

  choice : ∀ {k} {sessions : Session[ k ]}
    -> (∀ i -> Cmd A (sessions i))
    -> Cmd A (& sessions)

  close : Cmd A end

-----------------
-- Interpreter --
-----------------
postulate
  Channel : Set -- Untyped raw channels
  primAccept : IO Channel -- accept a connection and return the channel
  primClose : Channel -> IO ⊤ -- close the connection
  primSend : ∀ {A : Set} -> A -> Channel -> IO ⊤ -- send a value of type A through the channel
  primRecv : ∀ {A : Set} -> Channel -> IO A -- receive a value of type A

exec : ∀ {A S} -> Cmd A S -> A -> Channel -> IO A
exec (send get cmd) state1 channel = do
  let (state2 , x) = get state1
  primSend x channel
  exec cmd state2 channel

exec (recv put cmd) state1 channel = do
  x <- primRecv channel
  let state2 = put x state1
  exec cmd state2 channel

exec (select i cmd) state channel =
  primSend i channel >> exec cmd state channel

exec (choice cmdOf) state channel = do
  i <- primRecv channel
  exec (cmdOf i) state channel

exec close state channel =
  primClose channel >> pure state

-- Accepting a connection:
record Accepting A S : Set where
  constructor accept
  field cmd : Cmd A S

acceptor : ∀ {A S} -> Accepting A S -> A -> IO A
acceptor (accept cmd) a = primAccept >>= exec cmd a

--------------
-- Examples --
--------------
binaryp : Session
binaryp = ¿ int ∙ ¿ int ∙ ! int ∙ end

unaryp : Session
unaryp = ¿ int ∙ ! int ∙ end

negp-cmd : Cmd ℤ unaryp
negp-cmd = recv (λ x a -> x) $ send (λ a -> a , - a) close

addp-cmd : Cmd ℤ binaryp
addp-cmd = recv (λ x a -> x) $ recv (λ y a -> y + a) $ send (λ a -> a , a) close
