/-
Copyright (c) 2022 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir

! This file was ported from Lean 3 source module primitive
-/
import Jordan.Mathlib.Stabilizer
import Jordan.Mathlib.Pretransitive
import Jordan.Mathlib.Set
import Jordan.Mathlib.Partitions
import Jordan.SubMulActions

-- import Jordan.EquivariantMap
import Jordan.MaximalSubgroups
import Jordan.Blocks


import Mathlib.Data.Setoid.Partition
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.GroupTheory.GroupAction.SubMulAction
import Mathlib.GroupTheory.Subgroup.Simple
import Mathlib.GroupTheory.Abelianization
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Set.Card
import Mathlib.GroupTheory.GroupAction.Primitive

/-!
# Primitive actions

## Definitions

- `IsPreprimitive G X`
a structure that says that the action of a type `G`
on a type `X` (defined by an instance `SMul G X`) is *preprimitive*,
namely, it is pretransitive and the only blocks are ⊤ and subsingletons.
(The pretransitivity assumption is essentially trivial,
because orbits are blocks, unless the action itself is trivial.)

The notion which is introduced in classical books on group theory
is restricted to `mul_action` of groups.
In fact, it may be irrelevant if the action is degenerate,
when “trivial blocks” might not be blocks.
Moreover, the classical notion is *primitive*,
which assumes moreover that `X` is not empty.

- `IsQuasipreprimitive G X`
a structure that says that the `mul_action`
of the group `G` on the type `X` is *quasipreprimitive*,
namely, normal subgroups of `G` which act nontrivially act pretransitively.

- We prove some straightforward theorems that relate preprimitivity under equivariant maps, for images and preimages.

## Relation with stabilizers

- `isPreprimitive_of_block_order`
relates primitivity and the fact that the inclusion
order on blocks containing is simple.

- `maximal_stabilizer_iff_preprimitive`
an action is preprimitive iff the stabilizers of points are maximal subgroups.

## Relation with normal subgroups

- `IsPreprimitive.isQuasipreprimitive`
preprimitive actions are quasipreprimitive

## Particular results for actions on finite types

- `isPreprimitive_of_primeCard` :
a pretransitive action on a finite type of prime cardinal is preprimitive

- `isPreprimitive_of_large_image`
Given an equivariant map from a preprimitive action,
if the image is at least twice the codomain, then the codomain is preprimitive

- `Rudio`
Theorem of Rudio :
Given a preprimitive action of a group `G` on `X`, a finite `A : set X`
and two points, find a translate of `A` that contains one of them
and not the other one.
The proof relies on `is_block.of_subset` that itself requires finiteness of `A`,
but I don't know whether the theorem does…

-/

open MulAction

section Primitive

variable (G : Type _) (X : Type _)

variable {G X}

theorem IsTrivialBlock.of_card_le_2 [Fintype X] (hX : Fintype.card X ≤ 2) (B : Set X) :
    IsTrivialBlock B := by
  classical
  cases' le_or_lt (Fintype.card B) 1 with h1 h1
  · apply Or.intro_left
    rw [← Set.subsingleton_coe, ← Fintype.card_le_one_iff_subsingleton]
    exact h1
  · apply Or.intro_right
    rw [← set_fintype_card_eq_univ_iff]
    exact le_antisymm (set_fintype_card_le_univ B) (le_trans hX h1)

end Primitive

section EquivariantMap

variable {M : Type _} [Group M] {α : Type _} [MulAction M α]

variable {N β : Type _} [Group N] [MulAction N β]

theorem isPreprimitive_of_surjective_map {φ : M → N} {f : α →ₑ[φ] β} (hf : Function.Surjective f)
    (h : IsPreprimitive M α) : IsPreprimitive N β :=
  by
  have : IsPretransitive N β := isPretransitive.of_surjective_map hf h.toIsPretransitive
  apply IsPreprimitive.mk
  · intro B hB
    rw [← Set.image_preimage_eq B hf]
    apply IsTrivialBlock.image hf
    apply h.isTrivialBlock_of_isBlock
    apply hB.preimage

theorem isPreprimitive_of_bijective_map_iff {φ : M → N} {f : α →ₑ[φ] β} (hφ : Function.Surjective φ)
    (hf : Function.Bijective f) : IsPreprimitive M α ↔ IsPreprimitive N β :=
  by
  constructor
  apply isPreprimitive_of_surjective_map hf.surjective
  · intro hN
    haveI := (isPretransitive.of_bijective_map_iff hφ hf).mpr hN.toIsPretransitive
    apply IsPreprimitive.mk
    · intro B hB
      rw [← Set.preimage_image_eq B hf.injective]
      apply IsTrivialBlock.preimage hf.injective
      apply hN.isTrivialBlock_of_isBlock
      apply IsBlock_image f hφ hf.injective
      exact hB

end EquivariantMap

#lint
