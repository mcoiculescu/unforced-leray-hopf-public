import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.WeightedEnergy.LionsMagenesCyl.Mollifier.Defs

/-!
# Part III-a, `PartIII-a:T18/3/1/3/1` (`Mollifier`): the statements of the sub-tasks

Organizer file (no proofs except the assembly). Each `lmT_<n>` (`n = 1, 2, 3, 5, ..., 36`;

`Prop`, compiled here so that every task target is known to elaborate in the header of
`Mollifier/Defs.lean` (namespace `UnforcedLeray.Short.IIIa`; opens `Set MeasureTheory Filter
Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar`, scoped `ENNReal ContDiff Convolution`).
Source of record: `the November 2 reference manuscript` lines 3427-3440 and
3541-3552. The lemma task files import `Mollifier/Defs.lean` (and the files of their dependencies),
never this file; only the final assembly `LionsMagenesCyl/Mollifier.lean` imports it, to apply
`hasLMMollifier_of`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff Convolution

namespace UnforcedLeray.Short.IIIa

def lmT_1 : Prop := ∀ {c : ℝ} (hc : 0 < c) (k : ℕ), ContDiff ℝ ∞ (lmK c k)

def lmT_2 : Prop := ∀ {c : ℝ} (hc : 0 < c) (k : ℕ) (j : Fin 2) (z : ℝ × ℝ),
  B0579.pd j (lmK c k) z = B0579.pd j (lmRho c k) (lmPer c z)

def lmT_3 : Prop := ∀ {c : ℝ} (hc : 0 < c) (k : ℕ) (z : ℝ × ℝ), lmK c k (-z) = lmK c k z

def lmT_5 : Prop := ∀ {c : ℝ} (hc : 0 < c) {h : ℝ × ℝ → ℝ}
  (hh : ∀ z : ℝ × ℝ, c / 3 ≤ |z.1| → h z = 0) {g : ℝ × ℝ → ℂ}
  (hg : ∀ y : ℝ × ℝ, g (y.1 + c, y.2) = g y) (x : ℝ × ℝ),
  ∫ y in B0579.cell c, (h (lmPer c (x - y)) : ℂ) * g y = ∫ y, (h (x - y) : ℂ) * g y

def lmT_6 : Prop := ∀ {c : ℝ} (hc : 0 < c) (k : ℕ) (x : ℝ × ℝ),
  ∫ y in B0579.cell c, lmK c k (x - y) = 1

def lmT_7 : Prop := ∀ {c : ℝ} (hc : 0 < c) {h : ℝ × ℝ → ℝ} (hm : Measurable h) {M : ℝ}
  (hM : ∀ z : ℝ × ℝ, |h z| ≤ M) (hb : ∀ z : ℝ × ℝ, c / 3 ≤ |z.2| → h z = 0) (x : ℝ × ℝ)
  (p : ℝ≥0∞), MemLp (fun y => h (x - y)) p (volume.restrict (B0579.cell c))

def lmT_8 : Prop := ∀ {c : ℝ} (hc : 0 < c) (k : ℕ) {g : ℝ × ℝ → ℂ}
  (hg : MemLp g 2 (volume.restrict (B0579.cell c))) (x : ℝ × ℝ),
  Integrable (fun y => (lmK c k (x - y) : ℂ) * g y) (volume.restrict (B0579.cell c))

def lmT_9 : Prop := ∀ {c : ℝ} (hc : 0 < c) {g : ℝ × ℝ → ℂ}
  (hg : MemLp g 2 (volume.restrict (B0579.cell c))) (n : ℤ) (R : ℝ),
  IntegrableOn (lmExt c g) (Ico (n * c - c / 2) (n * c + c / 2) ×ˢ Icc (-R) R)

def lmT_10 : Prop := ∀ {c : ℝ} (hc : 0 < c) {g : ℝ × ℝ → ℂ}
  (hg : MemLp g 2 (volume.restrict (B0579.cell c))), LocallyIntegrable (lmExt c g)

def lmT_11 : Prop := ∀ {c : ℝ} (hc : 0 < c) (k : ℕ) {g : ℝ × ℝ → ℂ}
  (hg : MemLp g 2 (volume.restrict (B0579.cell c))),
  lmJs c k g = MeasureTheory.convolution (lmRho c k) (lmExt c g) (ContinuousLinearMap.lsmul ℝ ℝ)
    volume

def lmT_12 : Prop := ∀ {c : ℝ} (hc : 0 < c) (k : ℕ) {g : ℝ × ℝ → ℂ}
  (hg : MemLp g 2 (volume.restrict (B0579.cell c))), ContDiff ℝ ∞ (lmJs c k g)

def lmT_13 : Prop := ∀ {F : ℝ × ℝ → ℂ} {x : ℝ × ℝ} (hF : DifferentiableAt ℝ F x) (j : Fin 2),
  LMPd j F x = fderiv ℝ F x (B0579.dir j)

def lmT_14 : Prop := ∀ {c : ℝ} (hc : 0 < c) (k : ℕ) {g : ℝ × ℝ → ℂ}
  (hg : MemLp g 2 (volume.restrict (B0579.cell c))) (j : Fin 2) (x : ℝ × ℝ),
  LMPd j (lmJs c k g) x = ∫ y, (B0579.pd j (lmRho c k) (x - y) : ℂ) * lmExt c g y

def lmT_15 : Prop := ∀ {c : ℝ} (hc : 0 < c) (k : ℕ) {g : ℝ × ℝ → ℂ}
  (hg : MemLp g 2 (volume.restrict (B0579.cell c))) (j : Fin 2) (x : ℝ × ℝ),
  ∫ y, (B0579.pd j (lmRho c k) (x - y) : ℂ) * lmExt c g y =
    ∫ y in B0579.cell c, (B0579.pd j (lmK c k) (x - y) : ℂ) * g y

def lmT_16 : Prop := ∀ {c : ℝ} (hc : 0 < c) (k : ℕ) (x : ℝ × ℝ),
  B0579.IsCylTest c (fun y => lmK c k (x - y)) ∧
    ∀ (j : Fin 2) (y : ℝ × ℝ),
      B0579.pd j (fun y => lmK c k (x - y)) y = -B0579.pd j (lmK c k) (x - y)

def lmT_17 : Prop := ∀ {c : ℝ} (hc : 0 < c) (k : ℕ) {g : ℝ × ℝ → ℂ}
  (hg : MemLp g 2 (volume.restrict (B0579.cell c))) (j : Fin 2) (x : ℝ × ℝ),
  LMPd j (lmJs c k g) x =
    -∫ y in B0579.cell c, g y * (B0579.pd j (fun y => lmK c k (x - y)) y : ℂ)

def lmT_18 : Prop := ∀ {c : ℝ} (hc : 0 < c) (k : ℕ) {g h : ℝ × ℝ → ℂ} (j : Fin 2)
  (hgh : LMWeakPd c j g h) (x : ℝ × ℝ), LMPd j (lmJs c k g) x = lmJs c k h x

def lmT_19 : Prop := ∀ {c : ℝ} (hc : 0 < c) (k : ℕ) {f : ℝ × ℝ → ℂ} (hf : ContDiff ℝ ∞ f)
  (hper : ∀ y : ℝ × ℝ, f (y.1 + c, y.2) = f y) (j : Fin 2) (x : ℝ × ℝ),
  -∫ y in B0579.cell c, f y * (B0579.pd j (fun y => lmK c k (x - y)) y : ℂ) =
    ∫ y in B0579.cell c, (lmK c k (x - y) : ℂ) * LMPd j f y

def lmT_20 : Prop := ∀ {c : ℝ} (hc : 0 < c) (k : ℕ) (f : LMSpField)
  (hsm : ∀ i : Fin 2, ContDiff ℝ ∞ (fun x => f x i))
  (hper : ∀ (x : ℝ × ℝ) (i : Fin 2), f (x.1 + c, x.2) i = f x i) (hL2 : LMCellL2 c f)
  (hdiv : ∀ x : ℝ × ℝ, LMPd 0 (fun y => f y 0) x + LMPd 1 (fun y => f y 1) x = 0)
  (x : ℝ × ℝ), LMPd 0 (fun y => lmJ c k f y 0) x + LMPd 1 (fun y => lmJ c k f y 1) x = 0

def lmT_21 : Prop := ∀ {c : ℝ} (hc : 0 < c) (k : ℕ) {g : ℝ × ℝ → ℂ}
  (hg : MemLp g 2 (volume.restrict (B0579.cell c))) (x : ℝ × ℝ),
  ‖lmJs c k g x‖ ^ 2 ≤ ∫ y in B0579.cell c, lmK c k (x - y) * ‖g y‖ ^ 2

def lmT_22 : Prop := ∀ {c : ℝ} (hc : 0 < c) (k : ℕ) {g : ℝ × ℝ → ℂ}
  (hg : MemLp g 2 (volume.restrict (B0579.cell c))),
  Integrable (fun p : (ℝ × ℝ) × (ℝ × ℝ) => lmK c k (p.1 - p.2) * ‖g p.2‖ ^ 2)
    ((volume.restrict (B0579.cell c)).prod (volume.restrict (B0579.cell c)))

def lmT_23 : Prop := ∀ {c : ℝ} (hc : 0 < c) (k : ℕ) {g : ℝ × ℝ → ℂ}
  (hg : MemLp g 2 (volume.restrict (B0579.cell c))),
  ∫ x in B0579.cell c, ∫ y in B0579.cell c, lmK c k (x - y) * ‖g y‖ ^ 2 =
    ∫ y in B0579.cell c, ‖g y‖ ^ 2

def lmT_24 : Prop := ∀ {c : ℝ} (hc : 0 < c) (k : ℕ) {g : ℝ × ℝ → ℂ}
  (hg : MemLp g 2 (volume.restrict (B0579.cell c))),
  ∫ x in B0579.cell c, ‖lmJs c k g x‖ ^ 2 ≤ ∫ x in B0579.cell c, ‖g x‖ ^ 2

def lmT_25 : Prop := ∀ {c : ℝ} (hc : 0 < c) (k : ℕ) {g : ℝ × ℝ → ℂ}
  (hg : MemLp g 2 (volume.restrict (B0579.cell c))),
  MemLp (lmJs c k g) 2 (volume.restrict (B0579.cell c))

def lmT_26 : Prop := ∀ {c : ℝ} (hc : 0 < c) (k : ℕ) {f g : ℝ × ℝ → ℂ}
  (hf : MemLp f 2 (volume.restrict (B0579.cell c)))
  (hg : MemLp g 2 (volume.restrict (B0579.cell c))),
  Integrable (fun p : (ℝ × ℝ) × (ℝ × ℝ) =>
      (lmK c k (p.1 - p.2) : ℂ) * (starRingEnd ℂ (f p.2) * g p.1))
    ((volume.restrict (B0579.cell c)).prod (volume.restrict (B0579.cell c)))

def lmT_27 : Prop := ∀ {c : ℝ} (hc : 0 < c) (k : ℕ) {f g : ℝ × ℝ → ℂ}
  (hf : MemLp f 2 (volume.restrict (B0579.cell c)))
  (hg : MemLp g 2 (volume.restrict (B0579.cell c))),
  ∫ x in B0579.cell c, starRingEnd ℂ (lmJs c k f x) * g x =
    ∫ x in B0579.cell c, starRingEnd ℂ (f x) * lmJs c k g x

def lmT_28 : Prop := ∀ (c : ℝ) (k : ℕ) (f : ℝ × (ℝ × ℝ) → Fin 2 → ℂ)
  (hf : ∀ i : Fin 2, Measurable fun p => f p i) (i : Fin 2),
  Measurable fun p : ℝ × (ℝ × ℝ) => lmJ c k (fun y => f (p.1, y)) p.2 i

def lmT_29 : Prop := ∀ {c : ℝ} (hc : 0 < c) {g : ℝ × ℝ → ℂ}
  (hg : MemLp g 2 (volume.restrict (B0579.cell c))),
  ∀ᵐ x ∂(volume.restrict (B0579.cell c)), Tendsto (fun k : ℕ => lmJs c k g x) atTop (𝓝 (g x))

def lmT_30 : Prop := ∀ {α : Type} [MeasurableSpace α] {μ : Measure α} {H : ℕ → α → ℝ}
  {h : α → ℝ} (hH0 : ∀ k, 0 ≤ᵐ[μ] H k) (hHi : ∀ k, Integrable (H k) μ) (hi : Integrable h μ)
  (hae : ∀ᵐ x ∂μ, Tendsto (fun k => H k x) atTop (𝓝 (h x))) {ε : ℝ} (hε : 0 < ε),
  ∀ᶠ k in atTop, ∫ x, h x ∂μ - ε ≤ ∫ x, H k x ∂μ

def lmT_31 : Prop := ∀ {α : Type} [MeasurableSpace α] {μ : Measure α} {G : ℕ → α → ℂ}
  {g : α → ℂ} (hg : MemLp g 2 μ) (hG : ∀ k, MemLp (G k) 2 μ)
  (hle : ∀ k, ∫ x, ‖G k x‖ ^ 2 ∂μ ≤ ∫ x, ‖g x‖ ^ 2 ∂μ)
  (hae : ∀ᵐ x ∂μ, Tendsto (fun k => G k x) atTop (𝓝 (g x))),
  Tendsto (fun k => ∫ x, ‖G k x - g x‖ ^ 2 ∂μ) atTop (𝓝 0)

def lmT_32 : Prop := ∀ {c : ℝ} (hc : 0 < c) {g : ℝ × ℝ → ℂ}
  (hg : MemLp g 2 (volume.restrict (B0579.cell c))),
  Tendsto (fun k : ℕ => ∫ x in B0579.cell c, ‖lmJs c k g x - g x‖ ^ 2) atTop (𝓝 0)

def lmT_33 : Prop := ∀ {c : ℝ} (hc : 0 < c) (k : ℕ) (f g : LMSpField) (hf : LMCellL2 c f)
  (hg : LMCellL2 c g),
  ∫ x in B0579.cell c, ∑ i : Fin 2, starRingEnd ℂ (lmJ c k f x i) * g x i =
    ∫ x in B0579.cell c, ∑ i : Fin 2, starRingEnd ℂ (f x i) * lmJ c k g x i

def lmT_34 : Prop := ∀ {c : ℝ} (hc : 0 < c) (k : ℕ) (f : LMSpField) (hf : LMCellL2 c f),
  ∫ x in B0579.cell c, ∑ i : Fin 2, ‖lmJ c k f x i‖ ^ 2 ≤
    ∫ x in B0579.cell c, ∑ i : Fin 2, ‖f x i‖ ^ 2

def lmT_35 : Prop := ∀ {c : ℝ} (hc : 0 < c) (f : LMSpField) (hf : LMCellL2 c f),
  Tendsto (fun k : ℕ => ∫ x in B0579.cell c, ∑ i : Fin 2, ‖lmJ c k f x i - f x i‖ ^ 2) atTop
    (𝓝 0)

def lmT_36 : Prop := ∀ {c : ℝ} (hc : 0 < c) (k : ℕ) (z : ℝ × ℝ), ∃ n : ℤ,
  lmPer c z = (z.1 - n * c, z.2) ∧ ∀ᶠ w in 𝓝 z, lmK c k w = lmRho c k (w.1 - n * c, w.2)

/-- **Assembly of `HasLMMollifier` from the field lemmas** (checked here, so that the task
statements `lmT_8, lmT_12, lmT_18, lmT_20, lmT_25, lmT_28, lmT_33, lmT_34, lmT_35` are exactly the
clauses of `IsLMMollifier c (lmJ c)`; `periodic` and `smul` are `lmJ_periodic`, `lmJ_smul` of
`Mollifier/Defs.lean`). -/
theorem hasLMMollifier_of (h8 : lmT_8) (h12 : lmT_12) (h18 : lmT_18) (h20 : lmT_20)
    (h25 : lmT_25) (h28 : lmT_28) (h33 : lmT_33) (h34 : lmT_34) (h35 : lmT_35)
    (hG : ∀ {c : ℝ}, 0 < c → ∀ k : ℕ, ∃ C : ℝ, ∀ f : LMSpField, LMCellL2 c f → ∀ i j : Fin 2,
      MemLp (LMPd j (fun y => lmJ c k f y i)) 2 (volume.restrict (B0579.cell c)) ∧
        ∫ x in B0579.cell c, ‖LMPd j (fun y => lmJ c k f y i) x‖ ^ 2 ≤
          C * ∫ x in B0579.cell c, ∑ l : Fin 2, ‖f x l‖ ^ 2)
    (hW : ∀ {c : ℝ}, 0 < c → ∀ (k : ℕ) (f : LMSpField), LMCellL2 c f →
      (∀ ψ : ℝ × ℝ → ℝ, B0579.IsCylTest c ψ →
        ∫ x in B0579.cell c, (f x 0 * (B0579.pd 0 ψ x : ℂ) + f x 1 * (B0579.pd 1 ψ x : ℂ)) = 0) →
      ∀ x : ℝ × ℝ, LMPd 0 (fun y => lmJ c k f y 0) x + LMPd 1 (fun y => lmJ c k f y 1) x = 0) :
    HasLMMollifier := by
  intro c hc
  refine ⟨lmJ c, ?_⟩
  exact {
    smooth := fun k f hf i => h12 hc k (hf i)
    periodic := fun k f _ x i => lmJ_periodic hc.ne' k f x i
    add := fun k f g hf hg => by
      funext x i
      simp only [lmJ_apply, lmJs]
      simp_rw [mul_add]
      exact integral_add (h8 hc k (hf i) x) (h8 hc k (hg i) x)
    smul := fun k a f _ => lmJ_smul c k a f
    selfAdj := fun k f g hf hg => h33 hc k f g hf hg
    contr := fun k f hf => h34 hc k f hf
    commute := fun k f g j _ _ hw i x => h18 hc k j (hw i) x
    divFree := fun k f hsm hper hL2 hdiv x => h20 hc k f hsm hper hL2 hdiv x
    tendsto := fun f hf => h35 hc f hf
    memL2 := fun k f hf i => h25 hc k (hf i)
    measurable := fun k f hf i => h28 c k f hf i
    gradL2 := fun k => hG hc k
    divFreeWeak := fun k f hf hd x => hW hc k f hf hd x }

end UnforcedLeray.Short.IIIa
