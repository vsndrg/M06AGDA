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

C-zero : (n x : N) → C n (suc (x + n)) ≡ 0
C-zero 0 x = refl
C-zero (suc n) x =
  begin
    C (suc n) (suc (x + suc n))
    ≡⟨ cong (λ y → C n y + C n (suc y)) (plus-suc x n) ⟩ C n (suc (x + n)) + C n (suc (suc x + n)) 
    ≡⟨ cong (λ y → y + C n (suc (suc x + n))) (C-zero n x) ⟩ 0 + C n (suc (suc x + n)) 
    ≡⟨ C-zero n (suc x) ⟩ 0
  ∎

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

infixl 8 _^_
_^_ : N → N → N
_^_ a 0 = 1
_^_ a (suc n) = a * a ^ n

infixl 6 _⊕_
_⊕_ : (N → N) → (N → N) → (N → N)
_⊕_ f g = λ x → f x + g x

infixr 7 _×_
_×_ : N → (N → N) → (N → N)
_×_ 0 f = λ f → 0
_×_ (suc k) f = k × f ⊕ f

mul-f : (k : N) → (f : N → N) → (x : N) → (k × f) x ≡ k * f x
mul-f 0 f x = refl
mul-f (suc k) f x =
  begin
    (suc k × f) x
    ≡⟨⟩ (k × f ⊕ f) x
    ≡⟨⟩ (k × f) x + f x
    ≡⟨ cong (λ y → y + f x) (mul-f k f x) ⟩ k * f x + f x
    ≡⟨ add-comm (k * f x) (f x) ⟩ f x + k * f x 
    ≡⟨⟩ suc k * f x
  ∎

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

∑-distr-left : (f : N → N) → (k i n : N) → ∑ (k × f) i n ≡ k * (∑ f i n)
∑-distr-left f k i 0 = sym (mul-zero k)
∑-distr-left f k i (suc n) =
  begin
    ∑ (k × f) i (suc n)
    ≡⟨ ∑-assoc (k × f) i n ⟩ ∑ (k × f) i n + (k × f) (i + n)
    ≡⟨ cong (λ x → x + (k × f) (i + n)) (∑-distr-left f k i n) ⟩ k * (∑ f i n) + (k × f) (i + n)
    ≡⟨ cong (λ x → k * (∑ f i n) + x) (mul-f k f (i + n)) ⟩ k * (∑ f i n) + k * f (i + n)
    ≡⟨ distr-left k (∑ f i n) (f (i + n)) ⟩ k * (∑ f i n + f (i + n))
    ≡⟨ cong (λ x → k * x) (sym (∑-assoc f i n)) ⟩ k * (∑ f i (suc n))
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
∑-C 1 =
  begin
    ∑ (C 1) 0 (suc 1)
    ≡⟨⟩ C 1 0 + ∑ (C 1) 1 1
    ≡⟨⟩ C 1 0 + (C 1 1 + 0)
    ≡⟨ cong (λ x → C 1 0 + x) (plus-zero (C 1 1)) ⟩ C 1 0 + C 1 1
    ≡⟨⟩ 2
    ≡⟨ sym (mul-one 2) ⟩ 2 * 1
    ≡⟨⟩ 2 ^ 1
  ∎
∑-C (suc (suc m)) =
  begin
    ∑ (C (suc n)) 0 (suc (suc n))
    ≡⟨⟩ C (suc n) 0 + ∑ (C (suc n)) 1 (suc n)
    ≡⟨ cong (λ x → C (suc n) 0 + x) (∑-ind-shift (C (suc n)) (f ⊕ g) eq 0 (suc n)) ⟩ C (suc n) 0 + ∑ (f ⊕ g) 0 (suc n)
    ≡⟨⟩ C n 0 + ∑ (f ⊕ g) 0 (suc n)
    ≡⟨ cong (λ x → C n 0 + x) (∑-par-shift f g 0 n) ⟩ C n 0 + (C n 0 + ∑ (λ x → g x + f (suc x)) 0 n + C n (suc n))
    ≡⟨⟩ C n 0 + (C n 0 + ∑ (g ⊕ g) 0 n + C n (suc n))
    ≡⟨ cong (λ x → C n 0 + (C n 0 + ∑ (g ⊕ g) 0 n + x)) (C-zero n 0) ⟩ C n 0 + (C n 0 + ∑ (g ⊕ g) 0 n + 0)
    ≡⟨ cong (λ x → C n 0 + x) (plus-zero (C n 0 + ∑ (g ⊕ g) 0 n)) ⟩ C n 0 + (C n 0 + ∑ (g ⊕ g) 0 n)
    ≡⟨ add-assoc (C n 0) (C n 0) (∑ (g ⊕ g) 0 n) ⟩ C n 0 + C n 0 + ∑ (g ⊕ g) 0 n
    ≡⟨ cong (λ x → C n 0 + C n 0 + x) (sym (∑-ind-shift (f ⊕ f) (g ⊕ g) eq1 0 n)) ⟩ C n 0 + C n 0 + ∑ (f ⊕ f) 1 n
    ≡⟨⟩ ∑ (2 × f) 0 (suc n)
    ≡⟨ ∑-distr-left f 2 0 (suc n) ⟩ 2 * ∑ (C n) 0 (suc n)
    ≡⟨ cong (λ x → 2 * x) (∑-C (suc m)) ⟩ 2 * 2 ^ n
    ≡⟨⟩ 2 ^ suc n
  ∎
  where
    n = suc m
    f g : N → N
    f = λ x → C n x
    g = λ x → C n (suc x)
    eq : (j : N) → C (suc n) (suc j) ≡ (f ⊕ g) j
    eq j = refl
    eq1 : (j : N) → (f ⊕ f) (suc j) ≡ (g ⊕ g) j
    eq1 j = refl

