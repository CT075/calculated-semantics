open import Data.Nat
open import Data.Bool hiding (T)
open import Data.Maybe
open import Data.Empty
open import Data.Unit

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

variable
  T : Set

record ∃ (A : Set) (B : A -> Set) : Set where
  constructor pack_as_
  field
    proj₁ : A
    proj₂ : B proj₁

syntax ∃ A (λ x → B) = ∃[ x ∶ A ] B

unpack : ∀{A B} -> ∃ A B -> ((proj₁ : A) -> B proj₁ -> T) -> T
unpack (pack proj₁ as proj₂) f = f proj₁ proj₂

---- Source language

-- parameterized by whether it steps
data Exp : Bool -> Set where
  valB : Bool -> Exp false
  valN : ℕ -> Exp false
  add : ∀{b1 b2} -> Exp b1 -> Exp b2 -> Exp true
  if : ∀{b b1 b2} -> Exp b -> Exp b1 -> Exp b2 -> Exp true

---- Typing
infix 4 ⊢_∶_

data Ty : Set where
  nat : Ty
  bool : Ty

denot : Ty -> Set
denot nat = ℕ
denot bool = Bool

data ⊢_∶_ : ∀{b : Bool} -> Exp b -> Ty -> Set where
  typ-bool : ∀{b : Bool} -> ⊢(valB b) ∶ bool
  typ-int : ∀{i : ℕ} -> ⊢(valN i) ∶ nat
  typ-add : ∀{b1 b2 : Bool} {e1 : Exp b1} {e2 : Exp b2} ->
    ⊢ e1 ∶ nat -> ⊢ e2 ∶ nat -> ⊢ (add e1 e2) ∶ nat
  typ-if : ∀{b b1 b2 τ} {e : Exp b} {e1 : Exp b1} {e2 : Exp b2} ->
    ⊢ e ∶ bool -> ⊢ e1 ∶ τ -> ⊢ e2 ∶ τ -> ⊢ (if e e1 e2) ∶ τ

matchType : (τ1 : Ty) -> (τ2 : Ty) -> Maybe (τ1 ≡ τ2)
matchType nat nat = just refl
matchType bool bool = just refl
matchType _ _ = nothing

matchTypeEquiv : ∀{τ : Ty} -> (matchType τ τ ≡ just refl)
matchTypeEquiv {nat} = refl
matchTypeEquiv {bool} = refl

synthtype : ∀{b} -> Exp b -> Maybe Ty
synthtype (valB _) = just bool
synthtype (valN _) = just nat
synthtype (add e1 e2) =
  synthtype e1 >>= (λ τ1 ->
    matchType τ1 nat >>= (λ _ ->
      synthtype e2 >>= (λ τ2 ->
        matchType τ2 nat >>= (λ _ ->
          just nat
        ))))
synthtype (if e e1 e2) =
  synthtype e >>= (λ τ ->
    matchType τ bool >>= (λ _ ->
      synthtype e1 >>= (λ τ1 ->
        synthtype e2 >>= (λ τ2 ->
          matchType τ1 τ2 >>= (λ _ ->
            just τ1
          )))))

-- This function encodes the [e -> e'] judgment, and so encodes half of
-- the progress theorem.
step : ∀{e : Exp true}{τ : Ty} -> ⊢ e ∶ τ -> ∃[ b ∶ Bool ] (Exp b)
step {add {true} {_} e1 e2}{nat} (typ-add p1 p2) =
  pack true as (add (∃.proj₂ (step {e1} p1)) e2)
step {add {false} {true} e1 e2}{nat} (typ-add p1 p2) =
  pack true as (add e1 (∃.proj₂ (step {e2} p2)))
step {add (valN n1) (valN n2)} (typ-add _ _) =
  pack false as (valN (n1 + n2))
step {if {true} e e1 e2} (typ-if p p1 p2) =
  pack true as (if (∃.proj₂ (step {e} p)) e1 e2)
step {if {false} {b1} {b2} (valB b) e1 e2} (typ-if _ _ _) =
  if b then (pack b1 as e1) else (pack b2 as e2)

addNoBool : ∀{b : Bool} -> ⊢ (valB b) ∶ nat -> ⊥
addNoBool ()

ifNoNat : ∀{n : ℕ} -> ⊢ (valN n) ∶ bool -> ⊥
ifNoNat ()

matchTypeSemantics : ∀{τ} -> matchType τ τ ≡ just (refl {x = τ})
matchTypeSemantics {nat} = refl
matchTypeSemantics {bool} = refl

typeCorrectLHS : ∀{b : Bool}{e : Exp b}{τ : Ty} ->
  ⊢ e ∶ τ -> (synthtype e ≡ just τ)
typeCorrectLHS {_}{valB _} {bool} typ-bool = refl
typeCorrectLHS {_}{valN _} {nat} typ-int = refl
typeCorrectLHS {_}{add e1 e2} {nat} (typ-add p1 p2) = begin
    synthtype (add e1 e2)
  ≡⟨ refl ⟩ -- definition
    (synthtype e1 >>= (λ τ1 -> matchType τ1 nat >>= (λ _ ->
      synthtype e2 >>= (λ τ2 -> matchType τ2 nat >>= (λ _ -> just nat)))))
  ≡⟨ cong
      (λ n -> n >>= (λ τ1 -> matchType τ1 nat >>= (λ _ ->
        synthtype e2 >>= (λ τ2 -> matchType τ2 nat >>= (λ _ -> just nat)))))
      (typeCorrectLHS {_} {e1} {nat} p1) ⟩ -- IH e1
    (just nat >>= (λ τ1 -> matchType τ1 nat >>= (λ _ ->
      synthtype e2 >>= (λ τ2 -> matchType τ2 nat >>= (λ _ -> just nat)))))
  ≡⟨ refl ⟩ -- definition of (>>=) and matchType
    (synthtype e2 >>= (λ τ2 -> matchType τ2 nat >>= (λ _ -> just nat)))
  ≡⟨ cong
      (λ n -> n >>= (λ τ2 -> matchType τ2 nat >>= (λ _ -> just nat)))
      (typeCorrectLHS {_} {e2} {nat} p2) ⟩ -- IH e2
    (just nat >>= (λ τ2 -> matchType τ2 nat >>= (λ _ -> just nat)))
  ≡⟨ refl ⟩
    just nat
  ∎
typeCorrectLHS {_}{if e e1 e2} {τ} (typ-if p p1 p2) = begin
    synthtype (if e e1 e2)
  ≡⟨ refl ⟩ -- definition
    (synthtype e >>= (λ τ ->
      matchType τ bool >>= (λ _ ->
        synthtype e1 >>= (λ τ1 ->
          synthtype e2 >>= (λ τ2 ->
            matchType τ1 τ2 >>= (λ _ ->
              just τ1))))))
  ≡⟨ cong
       (λ n -> n >>= (λ τ ->
         matchType τ bool >>= (λ _ ->
           synthtype e1 >>= (λ τ1 ->
             synthtype e2 >>= (λ τ2 ->
               matchType τ1 τ2 >>= (λ _ ->
                 just τ1))))))
       (typeCorrectLHS {_} {e} {bool} p)⟩ -- IH e
     (just bool >>= (λ τ ->
       matchType τ bool >>= (λ _ ->
         synthtype e1 >>= (λ τ1 ->
           synthtype e2 >>= (λ τ2 ->
             matchType τ1 τ2 >>= (λ _ ->
               just τ1))))))
  ≡⟨ refl ⟩ -- definition of (>>=) and matchType
     (synthtype e1 >>= (λ τ1 ->
       synthtype e2 >>= (λ τ2 ->
         matchType τ1 τ2 >>= (λ _ -> just τ1))))
  ≡⟨ cong
       (λ n -> n >>= (λ τ1 ->
         synthtype e2 >>= (λ τ2 ->
           matchType τ1 τ2 >>= (λ _ -> just τ1))))
       (typeCorrectLHS {_} {e1} {τ} p1) ⟩ -- IH e1
     (just τ >>= (λ τ1 ->
       synthtype e2 >>= (λ τ2 ->
         matchType τ1 τ2 >>= (λ _ -> just τ1))))
  ≡⟨ refl ⟩
     (synthtype e2 >>= (λ τ2 ->
       matchType τ τ2 >>= (λ _ -> just τ)))
  ≡⟨ cong
       (λ n -> n >>= (λ τ2 -> matchType τ τ2 >>= (λ _ -> just τ)))
       (typeCorrectLHS {_} {e2} {τ} p2) ⟩ -- IH e2
     (just τ >>= (λ τ2 -> matchType τ τ2 >>= (λ _ -> just τ)))
  ≡⟨ refl ⟩
     (matchType τ τ >>= (λ _ -> just τ))
  ≡⟨ cong (λ n -> n >>= (λ _ -> just τ)) (matchTypeEquiv {τ}) ⟩
     (just (refl {x = τ}) >>= (λ _ -> just τ))
  ≡⟨ refl ⟩
     just τ
  ∎

preservation : ∀{e : Exp true}{τ : Ty} -> (p : ⊢ e ∶ τ) ->
    (synthtype e ≡ synthtype (∃.proj₂ (step {e} p)))
preservation {add {true} {_} e1 e2} {nat} (typ-add p1 p2) = begin
    synthtype (add e1 e2)
  ≡⟨ refl ⟩ -- definition
    (synthtype e1 >>= (λ τ1 -> matchType τ1 nat >>= (λ _ ->
      synthtype e2 >>= (λ τ2 -> matchType τ2 nat >>= (λ _ -> just nat)))))
  ≡⟨ cong
     (λ ty -> ty >>= (λ τ1 -> matchType τ1 nat >>= (λ _ ->
       synthtype e2 >>= (λ τ2 -> matchType τ2 nat >>= (λ _ -> just nat)))))
     (preservation {e1} p1) ⟩ -- IH
    (synthtype (∃.proj₂ (step {e1} p1)) >>= (λ τ1 -> matchType τ1 nat >>= (λ _ ->
      synthtype e2 >>= (λ τ2 -> matchType τ2 nat >>= (λ _ -> just nat)))))
  ≡⟨ refl ⟩ -- definition of [synthtype], step backwards
    synthtype (add (∃.proj₂ (step {e1} p1)) e2)
  ∎
preservation {add {false} {true} e1 e2} {nat} (typ-add p1 p2) = begin
    synthtype (add e1 e2)
  ≡⟨ refl ⟩ -- definition
    (synthtype e1 >>= (λ τ1 -> matchType τ1 nat >>= (λ _ ->
      synthtype e2 >>= (λ τ2 -> matchType τ2 nat >>= (λ _ -> just nat)))))
  ≡⟨ cong
     (λ ty -> synthtype e1 >>= (λ τ1 -> matchType τ1 nat >>= (λ _ ->
       ty >>= (λ τ2 -> matchType τ2 nat >>= (λ _ -> just nat)))))
     (preservation {e2} p2) ⟩ -- IH
    (synthtype e1 >>= (λ τ1 -> matchType τ1 nat >>= (λ _ ->
      synthtype (∃.proj₂ (step {e2} p2)) >>= (λ τ2 ->
        matchType τ2 nat >>= (λ _ -> just nat)))))
  ≡⟨ refl ⟩ -- definition of [synthtype], step backwards
    synthtype (add e1 (∃.proj₂ (step {e2} p2)))
  ∎
-- TODO: This actually looks pretty close to the paper version, but it'd be nice
-- to get a continuous chain.
preservation {add {false} {false} (valN n1) (valN n2)} (typ-add typ-int typ-int) =
    trans beforeStep afterStep
  where
    beforeStep : synthtype (add (valN n1) (valN n2)) ≡ just nat
    beforeStep = begin
        synthtype (add (valN n1) (valN n2))
      ≡⟨ refl ⟩
        just nat
      ∎

    afterStep :
      just nat ≡
      synthtype (∃.proj₂ (step {add (valN n1) (valN n2)} (typ-add typ-int typ-int)))
    afterStep = sym (begin
        synthtype (∃.proj₂ (step {add (valN n1) (valN n2)} (typ-add typ-int typ-int)))
      ≡⟨ cong (λ x -> synthtype (∃.proj₂ {Bool}{Exp} x)) stepStep ⟩
        synthtype {false} (∃.proj₂ {Bool}{Exp} (pack false as (valN (n1 + n2))))
      ≡⟨ cong synthtype stepProj ⟩
        synthtype {false} (valN (n1 + n2))
      ≡⟨ refl ⟩
        just nat
      ∎)
      where
        stepStep :
          step {add (valN n1) (valN n2)} (typ-add typ-int typ-int) ≡
          pack false as (valN (n1 + n2))
        stepStep = begin
            step {add (valN n1) (valN n2)} (typ-add typ-int typ-int)
          ≡⟨ refl ⟩
            pack false as (valN (n1 + n2))
          ∎

        stepProj :
          ∃.proj₂ {Bool}{Exp} (pack false as (valN (n1 + n2))) ≡
          valN (n1 + n2)
        stepProj = begin
            ∃.proj₂ {Bool}{Exp} (pack false as (valN (n1 + n2)))
          ≡⟨ refl ⟩
            valN (n1 + n2)
          ∎
preservation {add (valB b) e2} (typ-add p1 p2) = ⊥-elim (addNoBool p1)
preservation {add e1 (valB b)} (typ-add p1 p2) = ⊥-elim (addNoBool p2)
preservation {if {true} e e1 e2} (typ-if p p1 p2) = begin
    synthtype (if {true} e e1 e2)
  ≡⟨ refl ⟩ -- definition
    (synthtype e >>= (λ τ ->
      matchType τ bool >>= (λ _ ->
        synthtype e1 >>= (λ τ1 ->
          synthtype e2 >>= (λ τ2 ->
            matchType τ1 τ2 >>= (λ _ ->
              just τ1
            ))))))
  ≡⟨ cong
    (λ ty -> ty >>= (λ τ ->
      matchType τ bool >>= (λ _ ->
        synthtype e1 >>= (λ τ1 ->
          synthtype e2 >>= (λ τ2 ->
            matchType τ1 τ2 >>= (λ _ ->
              just τ1
            ))))))
      (preservation {e} p) ⟩ -- IH
    (synthtype (∃.proj₂ (step {e} p)) >>= (λ τ ->
      matchType τ bool >>= (λ _ ->
        synthtype e1 >>= (λ τ1 ->
          synthtype e2 >>= (λ τ2 ->
            matchType τ1 τ2 >>= (λ _ ->
              just τ1
            ))))))
  ≡⟨ refl ⟩ -- definition of [synthtype], step backwards
    synthtype (if (∃.proj₂ (step {e} p)) e1 e2)
  ∎
preservation {if {false} (valN n) e1 e2} {τ} (typ-if p p1 p2) = ⊥-elim (ifNoNat p)
preservation {if {false} (valB true) e1 e2} {τ} (typ-if p p1 p2) = begin
    synthtype (if (valB true) e1 e2)
  ≡⟨ refl ⟩ -- definition of [synthtype] and (>>=)
    (synthtype e1 >>= (λ τ1 ->
      synthtype e2 >>= (λ τ2 ->
        matchType τ1 τ2 >>= (λ _ -> just τ1))))
  ≡⟨ cong
       (λ ty -> ty >>= (λ τ1 ->
         synthtype e2 >>= (λ τ2 ->
           matchType τ1 τ2 >>= (λ _ -> just τ1))))
       (typeCorrectLHS p1) ⟩ -- [synthtype] correctness
    (just τ >>= (λ τ1 ->
      synthtype e2 >>= (λ τ2 ->
        matchType τ1 τ2 >>= (λ _ -> just τ1))))
  ≡⟨ refl ⟩ -- definition of (>>=)
    (synthtype e2 >>= (λ τ2 ->
      matchType τ τ2 >>= (λ _ -> just τ)))
  ≡⟨ cong
       (λ ty -> ty >>= (λ τ2 ->
         matchType τ τ2 >>= (λ _ -> just τ)))
       (typeCorrectLHS p2) ⟩ -- [synthtype] correctness
    (just τ >>= (λ τ2 ->
      matchType τ τ2 >>= (λ _ -> just τ)))
  ≡⟨ refl ⟩ -- definition of (>>=)
    (matchType τ τ >>= (λ _ -> just τ))
  ≡⟨ cong
       (λ pf -> pf >>= (λ _ -> just τ))
       (matchTypeSemantics {τ}) ⟩ -- definition of [matchType]
    (just (refl {x = τ}) >>= (λ _ -> just τ))
  ≡⟨ refl ⟩ -- definition of (>>=)
    just τ
  ≡⟨ sym (typeCorrectLHS p1) ⟩
    synthtype e1
  ∎
preservation {if {false} (valB false) e1 e2} {τ} (typ-if p p1 p2) = begin
    synthtype (if (valB true) e1 e2)
  ≡⟨ refl ⟩ -- definition of [synthtype] and (>>=)
    (synthtype e1 >>= (λ τ1 ->
      synthtype e2 >>= (λ τ2 ->
        matchType τ1 τ2 >>= (λ _ -> just τ1))))
  ≡⟨ cong
       (λ ty -> ty >>= (λ τ1 ->
         synthtype e2 >>= (λ τ2 ->
           matchType τ1 τ2 >>= (λ _ -> just τ1))))
       (typeCorrectLHS p1) ⟩ -- [synthtype] correctness
    (just τ >>= (λ τ1 ->
      synthtype e2 >>= (λ τ2 ->
        matchType τ1 τ2 >>= (λ _ -> just τ1))))
  ≡⟨ refl ⟩ -- definition of (>>=)
    (synthtype e2 >>= (λ τ2 ->
      matchType τ τ2 >>= (λ _ -> just τ)))
  ≡⟨ cong
       (λ ty -> ty >>= (λ τ2 ->
         matchType τ τ2 >>= (λ _ -> just τ)))
       (typeCorrectLHS p2) ⟩ -- [synthtype] correctness
    (just τ >>= (λ τ2 ->
      matchType τ τ2 >>= (λ _ -> just τ)))
  ≡⟨ refl ⟩ -- definition of (>>=)
    (matchType τ τ >>= (λ _ -> just τ))
  ≡⟨ cong
       (λ pf -> pf >>= (λ _ -> just τ))
       (matchTypeSemantics {τ}) ⟩ -- definition of [matchType]
    (just (refl {x = τ}) >>= (λ _ -> just τ))
  ≡⟨ refl ⟩ -- definition of (>>=)
    just τ
  ≡⟨ sym (typeCorrectLHS p2) ⟩
    synthtype e2
  ∎
