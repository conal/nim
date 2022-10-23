open import Data.Nat 

module Nim where

open import Level using (0ℓ)
open import Data.Fin hiding (_+_;_<_)
import Data.Fin.Properties as Fₚ
open import Data.Vec
open import Data.Product
open import Data.Empty
open import Data.Sum
open import Relation.Nullary
open import Relation.Binary
open import Function using (_on_; case_of_)
open import Relation.Binary.PropositionalEquality; open ≡-Reasoning
import Data.Nat.Properties as ℕₚ
import Relation.Binary.Construct.On as On
open import Induction.WellFounded using (WellFounded; Acc; acc)
import Data.Nat.Induction as ℕ
open import Data.Vec.Relation.Unary.All using (All; []; _∷_)

-- A board (game state) of size n is n piles of stones.
Board : ℕ → Set
Board = Vec ℕ

private variable n : ℕ

-- A legal move is a choice of stone pile and one fewer than the number of
-- stones to take.
Move : Board n → Set
Move b = ∃ λ i → Fin (lookup b i)

-- Execute a legal move
move : ∀ b → Move b → Board n
move b (i , k) = b [ i ]≔ (lookup b i ℕ-ℕ suc k)

infix 4 _⊏_
_⊏_ : Rel (Board n) 0ℓ
_⊏_ = _<_ on sum

⊏-wellFounded : WellFounded (_⊏_ {n})
⊏-wellFounded = On.wellFounded sum ℕ.<-wellFounded

move-⊏ : ∀ (b : Board n) m → move b m ⊏ b
move-⊏ (suc n ∷ ns) (zero  , k) = ℕₚ.+-monoˡ-< (sum ns) (s≤s (Fₚ.nℕ-ℕi≤n n k))
move-⊏ (    n ∷ ns) (suc i , k) = ℕₚ.+-monoʳ-< n        (move-⊏ ns (i , k))

lose′ win′ : (b : Board n) → Acc _⊏_ b → Set
lose′ b (acc rs) = ∀   m → win′  (move b m) (rs _ (move-⊏ b m))
win′  b (acc rs) = ∃ λ m → lose′ (move b m) (rs _ (move-⊏ b m))

lose win : Board n → Set
lose b = lose′ b (⊏-wellFounded b)
win  b = win′  b (⊏-wellFounded b)

-- Next, devise some computable strategies for *deciding* whether a game is lost
-- or won. 

empty : Board n → Set
empty = All (_≡ 0)

-- move-0∷ : {b : Board n} → Move (0 ∷ b) → Move b
-- move-0∷ (suc i , k) = i , k

-- lose-0∷ : {b : Board n} → lose b → lose (0 ∷ b)
-- lose-0∷ q = {!!}

-- sum0→empty : (b : Board n) → sum b ≡ 0 → empty b
-- sum0→empty [] refl = []
-- sum0→empty (zero ∷ xs) Σ≡0 = refl ∷ sum0→empty xs Σ≡0

-- empty-stuck : ∀ {b : Board n} → empty b → ¬ Move b
-- empty-stuck {b = []} [] ()
-- empty-stuck {b = 0 ∷ b} (refl ∷ empty) m = empty-stuck empty (move-0∷ m)

empty-stuck : ∀ {b : Board n} → empty b → ¬ Move b
empty-stuck {b = []} [] ()
empty-stuck {b = 0 ∷ b} (refl ∷ 0s) (suc i , k) = empty-stuck 0s (i , k)

-- sum0-stuck : ∀ (b : Board n) → sum b ≡ 0 → ¬ Move b
-- sum0-stuck b Σ≡0 = empty-stuck (sum0→empty b Σ≡0)

lose-empty : {b : Board n} → empty b → lose b
lose-empty empty m = ⊥-elim (empty-stuck empty m)

-- brute : (b : Board n) → lose b ⊎ win b
-- brute b = case (sum b , inspect sum b) of λ
--   { (zero  , q) → {!q!}
--   ; (suc s , q) → {!!}
--    }

-- brute : (b : Board n) → lose b ⊎ win b
-- brute b with sum b
-- ... | p = {!!}

-- brute : (b : Board n) → lose b ⊎ win b
-- brute b with sum b | inspect sum b
-- ... | p | q = {!!}


-- brute : (b : Board n) → lose b ⊎ win b
-- brute b = case sum b of λ
--   { zero → {!!}
--   ; (suc x) → {!!}
--   }

brute : (b : Board n) → lose b ⊎ win b
brute [] = inj₁ (lose-empty [])
brute (zero ∷ b) with brute b
... | inj₁ x = {!x!}
... | inj₂ y = {!!}
brute (suc n ∷ b) = {!!}

