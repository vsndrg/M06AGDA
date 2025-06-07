data N : Set where
  zero : N
  suc : N → N

{-# BUILTIN NATURAL N #-}

open import Relation.Binary.PropositionalEquality as A
open A.≡-Reasoning

-- ===================
-- Addition naturals
-- ===================

infixl 6 _+_
_+_ : N → N → N
_+_ 0 x = x
_+_ (suc y) x = suc (y + x)

plus-zero : (x : N) → x + 0 ≡ x
plus-zero 0 = refl
plus-zero (suc x) = 
  begin
    suc x + 0 ≡⟨⟩ suc (x + 0)
    ≡⟨ cong suc (plus-zero x) ⟩ suc x
  ∎

add-assoc : (a b c : N) → a + (b + c) ≡ a + b + c
add-assoc 0 b c = refl
add-assoc (suc a) b c = cong suc (add-assoc a b c)

plus-suc : (a b : N) → a + suc b ≡ suc (a + b)
plus-suc 0 b = refl
plus-suc (suc a) b = cong suc (plus-suc a b)

add-comm : (a b : N) → a + b ≡ b + a
add-comm 0 b = sym (plus-zero b)
add-comm (suc a) b =
  begin
    suc a + b
    ≡⟨ cong suc (add-comm a b) ⟩ suc (b + a)
    ≡⟨ sym (plus-suc b a) ⟩ b + suc a
  ∎


-- ================
-- Binary numbers
-- ================

data B : Set where
  e : B
  _O : B → B
  _I : B → B

postulate
  eO : e ≡ e O

incr : (b : B) → B
incr e = e I
incr (b' O) = (b' I)
incr (b' I) = (incr b') O

bin-nat : (b : B) → N
bin-nat e = 0
bin-nat (b' O) = bin-nat b' + bin-nat b'
bin-nat (b' I) = suc (bin-nat b' + bin-nat b') 

nat-bin : (n : N) → B
nat-bin 0 = e
nat-bin (suc n') = incr (nat-bin n')

incr-eq-suc : (b : B) → bin-nat (incr b) ≡ suc (bin-nat b)
incr-eq-suc e = refl
incr-eq-suc (b O) = refl
incr-eq-suc (b I) =
  begin
    bin-nat (incr (b I))
    ≡⟨ cong (λ x → x + x) (incr-eq-suc b) ⟩ suc (bin-nat b) + suc (bin-nat b)
    ≡⟨⟩ suc (bin-nat b + suc (bin-nat b))
    ≡⟨ cong suc (plus-suc (bin-nat b) (bin-nat b)) ⟩ suc (suc (bin-nat b + bin-nat b))
    ≡⟨⟩ suc (bin-nat (b I))
  ∎

add-self-eq-o : (n : N) → nat-bin (n + n) ≡ (nat-bin n) O
add-self-eq-o 0 = eO
add-self-eq-o (suc n) =
  begin
    nat-bin (suc n + suc n)
    ≡⟨⟩ nat-bin (suc (n + suc n))
    ≡⟨⟩ incr (nat-bin (n + suc n))
    ≡⟨ cong ( λ x → incr (nat-bin x)) (plus-suc n n) ⟩ incr (nat-bin (suc (n + n)))
    ≡⟨⟩ incr (incr (nat-bin (n + n)))
    ≡⟨ cong (λ x → incr (incr x)) (add-self-eq-o n) ⟩ incr (incr ((nat-bin n) O)) 
    ≡⟨⟩ incr ((nat-bin n) I)
    ≡⟨⟩ incr (nat-bin n) O
    ≡⟨⟩ (nat-bin (suc n)) O
  ∎

nat-bin-nat-id : (n : N) → bin-nat (nat-bin n) ≡ n
nat-bin-nat-id 0 = refl
nat-bin-nat-id (suc n) =
  begin
    bin-nat (nat-bin (suc n))
    ≡⟨⟩ bin-nat (incr (nat-bin n))
    ≡⟨ incr-eq-suc (nat-bin n) ⟩ suc (bin-nat (nat-bin n))
    ≡⟨ cong suc (nat-bin-nat-id n) ⟩ suc n
  ∎

bin-nat-bin-id : (b : B) → nat-bin (bin-nat b) ≡ b
bin-nat-bin-id e = refl
bin-nat-bin-id (b O) = 
  begin
    nat-bin (bin-nat (b O))
    ≡⟨⟩ nat-bin ((bin-nat b) + (bin-nat b))
    ≡⟨ add-self-eq-o (bin-nat b) ⟩ (nat-bin (bin-nat b)) O
    ≡⟨ cong _O (bin-nat-bin-id b) ⟩ b O
  ∎
bin-nat-bin-id (b I) =
  begin
    nat-bin (bin-nat (b I))
    ≡⟨⟩ nat-bin (suc (bin-nat b + bin-nat b))
    ≡⟨⟩ incr (nat-bin (bin-nat b + bin-nat b))
    ≡⟨ cong incr (add-self-eq-o (bin-nat b)) ⟩ incr ((nat-bin (bin-nat b)) O)
    ≡⟨⟩ (nat-bin (bin-nat b)) I
    ≡⟨ cong _I (bin-nat-bin-id b)⟩ b I
  ∎
