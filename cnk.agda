module cnk where

open import nat

open import Relation.Binary.PropositionalEquality as A
open A.≡-Reasoning

-- Binoial coefficient function.
-- ARGUMENTS:
--   - total number of elements in the set:
--       n : N
--   - number of elements being chosen:
--       k : N
-- RETURNS:
--   (N) number of combinations.
--
C : N → N → N
C 0 0 = 1
C 0 (suc k) = 0
C (suc n) 0 = 1
C (suc n) (suc k) = C n k + C n (suc k)

-- Summator function.
-- ARGUMENTS:
--   - function to apply on each element:
--       f : (N → N)
--   - start index:
--       i : N
--   - number of elements to sum:
--       n : N
-- RETURNS:
--   (N) sum of elements.
--
∑ : (N → N) → N → N → N
∑ f i 0 = 0
∑ f i (suc n) = f i + ∑ f (suc i) n

infixl 6 _⊕_
_⊕_ : (N → N) → (N → N) → (N → N)
_⊕_ f g = λ x → f x + g x

infixl 8 _^_
_^_ : N → N → N
_^_ a 0 = 1
_^_ a (suc n) = a * a ^ n

∑-assoc : (f : N → N) → (i n : N) → ∑ f i (suc n) ≡ ∑ f i n + f (i + n)
∑-assoc f i 0 =
  begin
    ∑ f i (suc 0)
    ≡⟨⟩ f i + 0
    ≡⟨ plus-zero (f i) ⟩ f i
    ≡⟨ cong f (sym (plus-zero i)) ⟩ ∑ f i 0 + f (i + 0)
  ∎
∑-assoc f i (suc n) =
  begin
    ∑ f i (suc (suc n))
    ≡⟨⟩ f i + ∑ f (suc i) (suc n)
    ≡⟨ cong (λ x → f i + x) (∑-assoc f (suc i) n) ⟩ f i + (∑ f (suc i) n + f (suc i + n))
    ≡⟨ add-assoc (f i) (∑ f (suc i) n) (f (suc i + n)) ⟩ f i + ∑ f (suc i) n + f (suc i + n)
    ≡⟨⟩ ∑ f i (suc n) + f (suc i + n)
    ≡⟨ cong (λ x → ∑ f i (suc n) + f x) (sym (plus-suc i n)) ⟩ ∑ f i (suc n) + f (i + suc n)
  ∎

∑-ind-shift : (f g : N → N) → ((j : N) → f (suc j) ≡ g j) → 
              (i : N) → (n : N) → ∑ f (suc i) n ≡ ∑ g i n
∑-ind-shift f g eq i 0 = refl
∑-ind-shift f g eq i (suc n) =
  begin
    ∑ f (suc i) (suc n)
    ≡⟨ ∑-assoc f (suc i) n ⟩ ∑ f (suc i) n + f (suc i + n)
    ≡⟨ cong (λ x → x + f (suc i + n)) (∑-ind-shift f g eq i n) ⟩ ∑ g i n + f (suc (i + n))
    ≡⟨ cong (λ x → ∑ g i n + x) (eq (i + n)) ⟩ ∑ g i n + g (i + n)
    ≡⟨ sym (∑-assoc g i n) ⟩ ∑ g i (suc n)
  ∎

∑-par-shift : (f g : N → N) → (i n : N) → ∑ (f ⊕ g) i (suc n) ≡ f i + ∑ (λ x → g x + f (suc x)) i n + g (i + n)
∑-par-shift f g i 0 = 
  begin
    ∑ (f ⊕ g) i (suc 0)
    ≡⟨⟩ (f ⊕ g) i + ∑ (f ⊕ g) (suc i) 0
    ≡⟨⟩ (f ⊕ g) i + 0
    ≡⟨⟩ f i + g i + 0
    ≡⟨ sym (add-assoc (f i) (g i) 0) ⟩ f i + (g i + 0)
    ≡⟨ cong (λ x → f i + x) (add-comm (g i) 0) ⟩ f i + (0 + g i)
    ≡⟨ add-assoc (f i) 0 (g i) ⟩ f i + 0 + g i
    ≡⟨⟩ f i + ∑ (λ x → g x + f (suc x)) i 0 + g i
    ≡⟨ cong (λ x → f i + ∑ (λ x → g x + f (suc x)) i 0 + g x) (sym (plus-zero i)) ⟩ f i + ∑ (λ x → g x + f (suc x)) i 0 + g (i + 0)
  ∎
∑-par-shift f g i (suc n) =
  begin
    ∑ (f ⊕ g) i (suc (suc n))
    ≡⟨ ∑-assoc (f ⊕ g) i (suc n) ⟩ ∑ (f ⊕ g) i (suc n) + (f ⊕ g) (i + suc n)
    ≡⟨⟩ ∑ (f ⊕ g) i (suc n) + (f (i + suc n) + g (i + suc n))
    ≡⟨ add-assoc (∑ (f ⊕ g) i (suc n)) (f (i + suc n)) (g (i + suc n)) ⟩
      ∑ (f ⊕ g) i (suc n) + f (i + suc n) + g (i + suc n)
    ≡⟨ cong (λ x → ∑ (f ⊕ g) i (suc n) + f x + g (i + suc n)) (plus-suc i n) ⟩
      ∑ (f ⊕ g) i (suc n) + f (suc (i + n)) + g (i + suc n)
    ≡⟨ cong (λ x → x + f (suc (i + n)) + g (i + suc n)) (∑-par-shift f g i n) ⟩
      f i + ∑ (λ x → g x + f (suc x)) i n + g (i + n) + f (suc (i + n)) + g (i + suc n)
    ≡⟨ cong (λ x → x + g (i + suc n)) (sym (add-assoc (f i + ∑ (λ x → g x + f (suc x)) i n) (g (i + n)) (f (suc (i + n))))) ⟩
      f i + ∑ (λ x → g x + f (suc x)) i n + (g (i + n) + f (suc (i + n))) + g (i + suc n)
    ≡⟨⟩ f i + ∑ (λ x → g x + f (suc x)) i n + (λ x → g x + f (suc x)) (i + n) + g (i + suc n)
    ≡⟨ cong (λ x → x + g (i + suc n)) (sym (add-assoc (f i) (∑ (λ x → g x + f (suc x)) i n) ((λ x → g x + f (suc x)) (i + n)))) ⟩
      f i + (∑ (λ x → g x + f (suc x)) i n + (λ x → g x + f (suc x)) (i + n)) + g (i + suc n)
    ≡⟨ cong (λ x → f i + x + g (i + suc n)) (sym (∑-assoc (λ x → g x + f (suc x)) i n)) ⟩
      f i + ∑ (λ x → g x + f (suc x)) i (suc n) + g (i + suc n)
  ∎

∑-C : (n : N) → ∑ (C n) 0 (suc n) ≡ 2 ^ n
∑-C 0 = refl
∑-C 1 = refl
∑-C (suc (suc m)) =
  begin
    ∑ (C (suc n)) 0 (suc (suc n))
    ≡⟨⟩ C (suc n) 0 + ∑ (C (suc n)) 1 (suc n)
    ≡⟨ cong (λ x → C (suc n) 0 + x) (∑-ind-shift (C (suc n)) (f ⊕ g) eq 0 (suc n)) ⟩ C (suc n) 0 + ∑ (f ⊕ g) 0 (suc n)
    ≡⟨⟩ C n 0 + ∑ (f ⊕ g) 0 (suc n)
    ≡⟨ cong (λ x → C n 0 + x) (∑-par-shift f g 0 n) ⟩ C n 0 + (f 0 + ∑ (f ⊕ g) 0 n + g n)
    ≡⟨ ? ⟩ 2 ^ suc n
  ∎
  where
    n = suc m
    f g : N → N
    f = λ x → C n x
    g = λ x → C n (suc x)
    eq : (j : N) → (C (suc n)) (suc j) ≡ (f ⊕ g) j
    eq j = refl

{-
∑-C : (n : N) → ∑ (C n) 0 (suc n) ≡ 2 ^ n
∑-C 0 = refl
∑-C (suc n) =
  begin
    ∑ (C (suc n)) 0 (suc (suc n))
    ≡⟨ ∑-assoc (C (suc n)) 0 (suc n) ⟩ ∑ (C (suc n)) 0 (suc n) + C (suc n) (suc n)
    ≡⟨⟩ C (suc n) 0 + ∑ (C (suc n)) 1 n + C (suc n) (suc n)
    ≡⟨ cong (λ x → C (suc n) 0 + x + C (suc n) (suc n)) (∑-ind-shift (C (suc n)) (f ⊕ g) eq 0 n) ⟩
      C (suc n) 0 + ∑ (λ x → C n x + C n (suc x)) 0 n + C (suc n) (suc n)
    ≡⟨⟩ C (suc n) 0 + ∑ (f ⊕ g) 0 n + C (suc n) (suc n)
    ≡⟨ ? ⟩ 2 ^ suc n
  ∎
  where
    f g : N → N
    f = λ x → C n x
    g = λ x → C n (suc x)
    eq : (j : N) → (C (suc n)) (suc j) ≡ (f ⊕ g) j
    eq j = refl
-}

