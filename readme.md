## The game of Nim

This project explores the two-player game [Nim](https://en.wikipedia.org/wiki/Nim, formulated in Agda.
In this game, there are `n` piles of stones (some of may be empty).
Players take turns removing one or more stones from any single pile.
In this variation of Nim, the goal is to take the last stone on the board.
(More commonly the goal is instead to avoid doing so.)

The heart of the Agda formulation is a pair of functions:
```agda
win lose : Board n → Set
```
where a board (game state) of size `n` is `n` piles of stones:
```agda
Board : ℕ → Set
Board = Vec ℕ
```
A legal move is a choice of pile and one fewer than the number of stones to take:
```agda
Move : Board n → Set
Move b = ∃ λ i → Fin (lookup b i)

move : ∀ b → Move b → Board n
move b (i , k) = b [ i ]≔ (lookup b i ℕ-ℕ suc k)
```
where `_ℕ-ℕ_` (from `Data.Fin`) subtracts a `Fin (suc n)` from `n`.

A game is lost (for the current player) when every move leads to a winning game (for the other player).
A game is won (really, winnable) when there is at least one move leading to a lost game:
```agda
lose win : Board n → Set
lose b = ∀   m → win  (move b m)
win  b = ∃ λ m → lose (move b m)
```
Note that if `b` has no remaining stones, then there are no legal moves, so `lose b` holds vacuously.

This simple mutual recursion is indeed well-founded but too subtly for Agda's termination checker.
Since every move removes at least one stone from the board on each term, the total number of stones remaining diminishes on each step.
We can thus persuade Agda of this well-foundedness by adding an accessibility predicate argument to `lose` and `win`.

Next, devise some computable strategies for *deciding* (correctly computing) whether a game is lost or won. 
