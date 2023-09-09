open import Agda.Builtin.Int using (Int)
open import Data.Bool.Base using (Bool)
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
    int : Sort
    bool : Sort
    unit : Sort

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
    `_ : Var -> LocalSession
    end : LocalSession

  ----------------
  -- Global Type --
  ----------------
  data GlobalSession : Set
  data GlobalSessionAlt : Set
  data GlobalSessionComm : Set

  data GlobalSession where
    _∙_ : GlobalSessionComm -> GlobalSession -> GlobalSession
    _=>_match_ : Participant -> Participant -> List⁺ GlobalSessionAlt -> GlobalSession
    μ_∙_ : Var -> GlobalSession -> GlobalSession
    `_ : Var -> GlobalSession
    end : GlobalSession

  data GlobalSessionAlt where
    case_then_ : Message -> GlobalSession -> GlobalSessionAlt

  data GlobalSessionComm where
    _=>_[_] : Participant -> Participant -> Message -> GlobalSessionComm

  infixr 19 _∙_

  --------------
  -- Examples --
  --------------
  travelProtocol : GlobalSession
  travelProtocol =
      "Customer" => "Agency" [ "Hawaii" ⟨ unit ⟩ ]
    ∙ "Agency" => "Customer" [ "quote" ⟨ nat ⟩ ]
    ∙ "Customer" => "Agency" match (
        case "accept" ⟨ unit ⟩ then (
          "Customer" => "Agency" [ "address" ⟨ nat ⟩ ]
        ∙ "Agency" => "Customer" [ "date" ⟨ nat ⟩ ]
        ∙ end
        )
      ∷ case "reject" ⟨ unit ⟩ then end
      ∷ []
    )

  customer : LocalSession
  customer = ! "Hawaii" ⟨ unit ⟩ ∙ ¿ "quote" ⟨ nat ⟩ ∙ (accept ⊕ reject)
    where
      accept = ! "accept" ⟨ unit ⟩ ∙ ! "address" ⟨ nat ⟩ ∙ ¿ "date" ⟨ nat ⟩ ∙ end
      reject = ! "reject" ⟨ unit ⟩ ∙ end

  agency : LocalSession
  agency = ¿ "Hawaii" ⟨ unit ⟩ ∙ ! "quote" ⟨ nat ⟩ ∙ (accept & reject)
    where
      accept = ¿ "accept" ⟨ unit ⟩ ∙ ¿ "address" ⟨ nat ⟩ ∙ ! "data" ⟨ nat ⟩ ∙ end
      reject = ¿ "reject" ⟨ unit ⟩ ∙ end
