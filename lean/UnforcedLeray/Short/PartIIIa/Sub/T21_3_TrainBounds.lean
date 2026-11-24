import UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.FiniteTrainFluxVolterra
import UnforcedLeray.Short.PartI.TrainClass

/-!
# Part III-a, `PartIII-a:T21/3/1`: train coefficients on finite age horizons

Source of record: `the November 2 reference manuscript` (SP below).

## Why the coefficient bounds are not uniform in the age (`PartIII-a:T21/3/1/org`)

The global constructor `actualTrainFluxPathOfBounds` (`Cons/.../MixedEvolution/ActualTrainFluxPath.lean`)
asks for `|Vc tr t x i| ≤ Cv` and `|⟨x⟩^m Ec tr t x| ≤ CE` on the cell for **all ages `t ≥ 0`**
with one pair `(Cv, CE)`.  For `m > 8` the second bound is not a property of the actual train:

* the source bounds weighted train norms only on finite age intervals, with constants `P_S`
  polynomial in `1 + S` (SP 255-258; transverse tails `sct:transverse`, SP 460-467, "On each
  `0 ≤ s ≤ S_*`"; the fixed-band comparison, SP 2085-2092, "On `s ≤ Σ/ν` ... in any fixed finite
  weighted derivative budget"); its age-global statements (`sct:overlap`, SP 304-313;
  `sct:integrated`, SP 314-322) are unweighted;
* the age-uniform weighted bound fails whenever the leading coefficient `a₀` of the mean-stream
  expansion `sct:expansion` (SP 447-459) is non-zero: the horizontal mean of the vorticity is
  `∂_η² S`, `S = a₀ G_{νs} + O(...)`, so `sup_η ⟨η⟩^m |∂_η² S(η, s)| ≍ |a₀| (νs)^{(m-3)/2} → ∞`
  (consistently, the bound SP 458-459 for `S` itself grows like `(1+s)^{(m-b-1)/2}`), and the cell
  supremum of `⟨x⟩^m |Ec|` dominates the supremum of its weighted horizontal mean.

So no age-uniform `ActualTrainFluxPath` is available for the actual train, and a hypothesis
"uniform train bounds" could never be discharged by the main theorem.  It is not introduced.

## What the existence argument uses

The Volterra iteration for the full evolution (SP 2819-2836; the finite-interval construction
SP 2072-2095) reads the perturbation `B(r)ω = vω + E K_cω` only on bounded age strips, where the
train is bounded.  The horizon objects are:

* `TrainBoundsOn tr m T Cv CE`: the velocity and weighted-curl bounds on the ages `[0, T]`
  (exactly the fields `velocity_bound`, `weighted_curl_bound` of `ActualTrainFluxPathOn`,
  `Cons/.../MixedEvolution/FiniteTrainFluxVolterra.lean`);
* `FiniteHorizonTrainBounds tr m`: such constants exist for every horizon `T ≥ 0`;
* `TrainBoundsSmall`: every train of the BUC class at `c = ν^{-2}`, `ν` small, has finite-horizon
  bounds.  Its velocity half is `velocityBoundOn_of_isBUCTrain` below (BUC, SP 270-288); its curl
  half is the transverse-tail estimate SP 460-467 (`TrainTransverseTailsUniform`, whose threshold
  `ν₀` does not depend on the horizon) together with the BUC bound of `Dv` on the remaining band;
* `FluxContinuityOn`: strong continuity in the age of the clamped actual flux operator (dominated
  convergence from the joint continuity of the train and the bounds on `[0, T]`);
* `actualTrainFluxPathOnOfBounds`, `nonempty_actualTrainFluxPathOn`: the horizon flux path.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory

namespace UnforcedLeray.Short.IIIa.Exist

open UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution

/-- **Train coefficient bounds on the ages `[0, T]`** (SP 2819-2836, SP 270-288, SP 460-467):
`|v_i(s, x)| ≤ Cv` everywhere and `|⟨x⟩^m E(s, x)| ≤ CE` on the cell for `0 ≤ s ≤ T`, with
`v = Vc tr`, `E = Ec tr = curl v`.  The two conjuncts are the fields `velocity_bound`,
`weighted_curl_bound` of `ActualTrainFluxPathOn`. -/
def TrainBoundsOn {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) (m T Cv CE : ℝ) : Prop :=
  (∀ s : Icc (0 : ℝ) T, ∀ x i, |UnforcedLeray.B0238.Vc tr s x i| ≤ Cv) ∧
  (∀ s : Icc (0 : ℝ) T, ∀ x ∈ UnforcedLeray.B0579.cell c,
    |UnforcedLeray.B0579.bracket x ^ m * UnforcedLeray.B0238.Ec tr s x| ≤ CE)

/-- **Finite-horizon train bounds**: for every horizon `T ≥ 0` there are constants
`Cv, CE ≥ 0` (depending on `T`, polynomially in the source: `P_S`, SP 255-258) with
`TrainBoundsOn tr m T Cv CE`. -/
def FiniteHorizonTrainBounds {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) (m : ℝ) : Prop :=
  ∀ T : ℝ, 0 ≤ T → ∃ Cv CE : ℝ, 0 ≤ Cv ∧ 0 ≤ CE ∧ TrainBoundsOn tr m T Cv CE

/-- **The trains of the main theorem have finite-horizon bounds** (SP 270-288: the BUC train has
bounded velocity and derivatives on every `[0, S]`; SP 460-467: on each `0 ≤ s ≤ S_*` the
vorticity has transverse tails `P_{S_*}{e^{-bl/c} + e^{-bl²/(C₀+νS_*)}}` for
`|η| ≥ C/ν + 2 + l`, which absorb the weight `⟨x⟩^m` on the cell `|q| ≤ c/2`).  For `m > 8`
there is `ν₁ > 0` such that every BUC train at `c = ν^{-2}`, `0 < ν ≤ ν₁`, has
`FiniteHorizonTrainBounds tr m`. -/
def TrainBoundsSmall : Prop :=
  ∀ m : ℝ, 8 < m → ∃ ν₁ : ℝ, 0 < ν₁ ∧ ∀ ν : ℝ, 0 < ν → ν ≤ ν₁ →
    ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
      UnforcedLeray.Short.PartI.IsBUCTrain tr → FiniteHorizonTrainBounds tr m

/-- **Strong continuity of the clamped actual flux** (SP 2819-2836: `B(t)` is strongly
continuous): for bounds on `[0, T]` and a fixed state `w`, the age map
`t ↦ B(clamp t) w = v(clamp t) w + E(clamp t) K_c w` is continuous into the flux space.  This is the
field `continuous_flux_apply` of `ActualTrainFluxPathOn`; it follows by dominated convergence from
the joint continuity of `Vc tr`, `Ec tr` in `(s, x)` on `[0, ∞) × ℝ²` and the bounds. -/
def FluxContinuityOn : Prop :=
  ∀ (ν c m : ℝ) [Fact (0 < c)] (hm : 1 ≤ m) (tr : UnforcedLeray.B0140.TrainSol ν c)
    (T : ℝ) (hT : 0 ≤ T) (Cv CE : ℝ) (hCv : 0 ≤ Cv) (hCE : 0 ≤ CE)
    (hV : ∀ s : Icc (0 : ℝ) T, ∀ x i, |UnforcedLeray.B0238.Vc tr s x i| ≤ Cv)
    (hE : ∀ s : Icc (0 : ℝ) T, ∀ x ∈ UnforcedLeray.B0579.cell c,
      |UnforcedLeray.B0579.bracket x ^ m * UnforcedLeray.B0238.Ec tr s x| ≤ CE)
    (w : ActualVorticity (c := c) (m := m) hm),
    Continuous (fun t => actualTrainFluxAtNonneg (s := (actualTrainAgeClamp T hT t).1) hm tr
      (actualTrainAgeClamp T hT t).property.1 hCv hCE
      (hV (actualTrainAgeClamp T hT t)) (hE (actualTrainAgeClamp T hT t)) w)

/-- The horizon flux path of the actual train, from bounds on `[0, T]` and flux continuity. -/
def actualTrainFluxPathOnOfBounds (hcont : FluxContinuityOn) {ν c m : ℝ} [Fact (0 < c)]
    (hm : 1 ≤ m) (tr : UnforcedLeray.B0140.TrainSol ν c) {T : ℝ} (hT : 0 ≤ T)
    {Cv CE : ℝ} (hCv : 0 ≤ Cv) (hCE : 0 ≤ CE) (hB : TrainBoundsOn tr m T Cv CE) :
    ActualTrainFluxPathOn hm tr hT where
  Cv := Cv
  CE := CE
  hCv := hCv
  hCE := hCE
  velocity_bound := hB.1
  weighted_curl_bound := hB.2
  continuous_flux_apply := fun w => hcont ν c m hm tr T hT Cv CE hCv hCE hB.1 hB.2 w

/-- Finite-horizon bounds give a horizon flux path for every horizon. -/
theorem nonempty_actualTrainFluxPathOn (hcont : FluxContinuityOn) {ν c m : ℝ} [Fact (0 < c)]
    (hm : 1 ≤ m) (tr : UnforcedLeray.B0140.TrainSol ν c) (hB : FiniteHorizonTrainBounds tr m)
    {T : ℝ} (hT : 0 ≤ T) : Nonempty (ActualTrainFluxPathOn hm tr hT) := by
  obtain ⟨Cv, CE, hCv, hCE, h⟩ := hB T hT
  exact ⟨actualTrainFluxPathOnOfBounds hcont hm tr hT hCv hCE h⟩

/-- The velocity half of the finite-horizon bounds for a BUC train (SP 270-288). -/
theorem velocityBoundOn_of_isBUCTrain {ν c : ℝ} {tr : UnforcedLeray.B0140.TrainSol ν c}
    (h : UnforcedLeray.Short.PartI.IsBUCTrain tr) {T : ℝ} (hT : 0 ≤ T) :
    ∃ Cv : ℝ, 0 ≤ Cv ∧ ∀ s : Icc (0 : ℝ) T, ∀ x i, |UnforcedLeray.B0238.Vc tr s x i| ≤ Cv := by
  obtain ⟨M, hM⟩ := h.sup_bound hT
  refine ⟨max M 0, le_max_right _ _, fun s x i => ?_⟩
  have h1 : ‖tr.v s x i‖ ≤ ‖tr.v s x‖ := PiLp.norm_apply_le _ i
  have h2 := hM s s.2 x
  rw [Real.norm_eq_abs] at h1
  exact (h1.trans h2).trans (le_max_left _ _)

end UnforcedLeray.Short.IIIa.Exist
