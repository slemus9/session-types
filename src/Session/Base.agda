open import Data.Bool.Base hiding (if_then_else_)
open import Data.Integer.Base using (ℤ)
open import Data.List
open import Data.List.NonEmpty
open import Data.Nat.Base using (ℕ)
open import Data.String.Base using (String)
open import Data.Unit.Base using (⊤)

-- Based on http://mrg.doc.ic.ac.uk/publications/a-very-gentle-introduction-to-multiparty-session-types/main.pdf
module Session.Base where

-----------------
-- Definitions --
-----------------
Label = String
Participant = String
Var = String

data Sort : Set where
  nat : Sort
  bool : Sort

data Message : Set where
  _⟨_⟩ : Label -> Sort -> Message

----------------
-- Local Type --
----------------
data LocalSession : Set where
  !_∙_ : Message -> LocalSession -> LocalSession
  ¿_∙_ : Message -> LocalSession -> LocalSession
  _⊕_ : LocalSession -> LocalSession -> LocalSession
  _&_ : LocalSession -> LocalSession -> LocalSession
  μ_∙_ : Var -> LocalSession -> LocalSession
  var : Var -> LocalSession
  end : LocalSession

-----------------
-- Global Type --
-----------------
data GlobalSession : Set
data GlobalSessionAlt : Set
data GlobalSessionComm : Set

data GlobalSession where
  _∙_ : GlobalSessionComm -> GlobalSession -> GlobalSession
  _=>_match_ : Participant -> Participant -> List⁺ GlobalSessionAlt -> GlobalSession
  μ_∙_ : Var -> GlobalSession -> GlobalSession
  var : Var -> GlobalSession
  end : GlobalSession

data GlobalSessionAlt where
  case_then_ : Message -> GlobalSession -> GlobalSessionAlt

data GlobalSessionComm where
  _=>_[_] : Participant -> Participant -> Message -> GlobalSessionComm

-----------
-- Terms --
-----------
data Expr : Set -> Set where
  nat : ℕ -> Expr ℕ
  bool : Bool -> Expr Bool
  var : ∀ {A} -> Var -> Expr A
  succ : Expr ℕ -> Expr ℕ
  neg : Expr Bool -> Expr Bool
  _less_ : Expr ℕ -> Expr ℕ -> Expr Bool

data Process : Set1 where
  _∙_ : Process -> Process -> Process
  _+_ : Process -> Process -> Process
  if_then_else_ : Expr Bool -> Process -> Process -> Process
  _!_⟨_⟩ : ∀ {A} -> Participant -> Label -> Expr A -> Process
  _¿_⟨_⟩ : Participant -> Label -> Var -> Process
  μ_∙_ : Var -> Process -> Process
  var : Var -> Process
  end : Process

data MultipartyProcess : Set1 where
  _exec_ : Participant -> Process -> MultipartyProcess
  -- Represents the parallel composition of two processes:
  _<>_ : Process -> Process -> MultipartyProcess


infixl 19 _+_
infix 18 _less_
infixr 17 _∙_
infixl 16 _<>_

---------------
-- Functions --
---------------


--------------
-- Examples --
--------------
travelProtocol : GlobalSession
travelProtocol =
    "Customer" => "Agency" [ "Hawaii" ⟨ bool ⟩ ]
  ∙ "Agency" => "Customer" [ "quote" ⟨ nat ⟩ ]
  ∙ "Customer" => "Agency" match (
      case "accept" ⟨ bool ⟩ then (
        "Customer" => "Agency" [ "address" ⟨ nat ⟩ ]
      ∙ "Agency" => "Customer" [ "date" ⟨ nat ⟩ ]
      ∙ end
      )
    ∷ case "reject" ⟨ bool ⟩ then end
    ∷ []
  )

customer : LocalSession
customer = ! "Hawaii" ⟨ bool ⟩ ∙ ¿ "quote" ⟨ nat ⟩ ∙ (accept ⊕ reject)
  where
    accept = ! "accept" ⟨ bool ⟩ ∙ ! "address" ⟨ nat ⟩ ∙ ¿ "date" ⟨ nat ⟩ ∙ end
    reject = ! "reject" ⟨ bool ⟩ ∙ end

agency : LocalSession
agency = ¿ "Hawaii" ⟨ bool ⟩ ∙ ! "quote" ⟨ nat ⟩ ∙ (accept & reject)
  where
    accept = ¿ "accept" ⟨ bool ⟩ ∙ ¿ "address" ⟨ nat ⟩ ∙ ! "data" ⟨ nat ⟩ ∙ end
    reject = ¿ "reject" ⟨ bool ⟩ ∙ end

pCustomer : Process
pCustomer =
    "Agency" ! "Hawaii" ⟨ bool true ⟩
  ∙ "Agency" ¿ "quote" ⟨ "x" ⟩
  ∙ if (nat 1000 less var "x")
    then "Agency" ! "reject" ⟨ bool true ⟩ ∙ end
    else ("Agency" ! "accept" ⟨ bool true ⟩ ∙ end)

pAgency : Process
pAgency =
    "Customer" ¿ "Hawaii" ⟨ "x" ⟩
  ∙ "Customer" ! "quote" ⟨ nat 5000 ⟩
  ∙ (
      "Customer" ¿ "accept" ⟨ "_" ⟩ ∙ "Customer" ¿ "address" ⟨ "a" ⟩ ∙ "Customer" ! "date" ⟨ nat 25122019 ⟩ ∙ end
    + "Customer" ¿ "reject" ⟨ "_" ⟩ ∙ end
  )
