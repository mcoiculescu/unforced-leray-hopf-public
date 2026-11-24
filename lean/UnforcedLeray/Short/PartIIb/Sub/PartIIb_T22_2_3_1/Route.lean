import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T22_2_3
import UnforcedLeray.Short.PartIIb.Sub.T22_1.Plan

/-!


Source of record: `the November 2 reference manuscript` lines 2100-2105 (the
regular backward problem behind the duality argument: "one may smooth the weight ... to justify
this calculation"; "Duhamel for a smooth compactly supported datum"), with the comparison
`TrainClose` of lines 2085-2093.  The source treats the backward problem as standard parabolic
theory; this file fixes the Lean route.

## Route

The backward problem `φ_r + νΔφ + v·∇φ = 0`, `φ(t) = ψ` on `[s, t]` is the time reversal
`φ(r) = u(t - r)` of the forward problem `u_σ = νΔu - w·∇u`, `u(0) = ψ` on `[0, t - s]`, with the
reversed drift `w(σ) = -v(t - σ)` (`revDrift`).  The reversed drift is not a train velocity, but
the forward machinery of `PartII-b:T22/1` (`Sub/T22_1/Plan.lean`) is already stated for an
arbitrary drift with `CylCoeff` (bounded, `C¹`, periodic): `DuhamelExists` (Picard,
`T22/1/14`, `T22/1/15`) and `DuhamelToPde` (`T22/1/16`) apply to `w` verbatim; no generalized
statement is needed.  `CylCoeff` passes to `w` (`cylCoeff_revDrift`, proved here) and the train
velocity satisfies it for every `c > 0` (`TrainCylCoeff`; `TrainCoeffBdd` of `T22/1/1` is stated
for `c ≥ 1`).

What the Picard class gives: `C²` slices, periodicity (so no uniqueness/translation argument is
needed), the weighted bound `W2 · cosh ≤ B` (so no maximum principle is needed for boundedness),
the terminal value and the equation.  What it does not give is the joint `C^∞` regularity of
`BwdSol.smooth` (required by `CylEtaTest` of `Sub/T22_2.lean`).  `TrainClose` bounds only
`D^j v` for `j ≤ 4`, so this regularity is LOCAL: it is proved on the bands
`band ρ = {|η| < ρ}` (`LocCk`), by induction on the order (`LocBase`, `LocStep`), then assembled
(`LocAssemble`) into smooth slices with jointly continuous partials of every order (`SpSmooth`);
the time direction follows from the equation (`FwdJointSmooth`).

## Leaves

* `TrainCylCoeff` (`T22/1/1`-type, every `c > 0`): from `TcRegular` and `BwdDriftC2Bound`;
* `DuhamelExists` = `duhamelExists_of_parts picardIterates picardLimit` (`T22/1/14`, `/15`);
* `DuhamelToPde` (`T22/1/16`);
* `LocBase`: the Picard class is `LocCk 2` on every band;
* `LocStep`: `LocCk k` on `band (ρ + 3)` gives `LocCk (k + 1)` on `band ρ` (local parabolic
  regularity; the analytic core);
* `LocAssemble`: `LocCk k` on every band for every `k ≥ 2` gives `SpSmooth`;
* `FwdJointSmooth`: `SpSmooth` and the equation give joint `C^∞` in `(σ, x)`.

`bwdExists_of_route` proves `BwdExists` from these; the time reversal, the terminal value,
periodicity, boundedness and the backward equation are proved here.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open UnforcedLeray.Cons.C03.Concrete

namespace UnforcedLeray.Short.IIb

namespace BwdRoute

open CylPDE

/-! ## Objects -/

/-- The reversed drift `w(σ) = -v(t - σ)` of the forward problem. -/
def revDrift (t : ℝ) (v : ℝ → Pl → UnforcedLeray.Train.Vec) : ℝ → Pl → UnforcedLeray.Train.Vec :=
  fun σ x => -v (t - σ) x

/-- The iterated partial derivative along a word: `pdW [j₁, …, j_m] g = ∂_{j₁} ⋯ ∂_{j_m} g`. -/
def pdW : List (Fin 2) → (Pl → ℝ) → Pl → ℝ
  | [], g => g
  | j :: l, g => B0579.pd j (pdW l g)

/-- The band `{x : |η| < ρ}` (`η = x.2`); it is `c`-periodic in `q = x.1`. -/
def band (ρ : ℝ) : Set Pl := {x : Pl | |x.2| < ρ}

/-- The forward equation `u_σ = νΔu - w·∇u` on `[0, T]`, one-sided at the ends (the form of
`DuhamelToPde` with `s = 0`). -/
def FwdPde (ν T : ℝ) (w : ℝ → Pl → UnforcedLeray.Train.Vec) (u : ℝ → Pl → ℝ) : Prop :=
  ∀ σ ∈ Icc 0 T, ∀ x : Pl,
    HasDerivWithinAt (fun r => u r x)
      (ν * lapP (u σ) x - (w σ x 0 * B0579.pd 0 (u σ) x + w σ x 1 * B0579.pd 1 (u σ) x))
      (Icc 0 T) σ

/-- The forward problem as produced by the `T22/1` machinery for a smooth drift: `w` is a
`CylCoeff` drift, jointly `C^∞` on `[0, T] × ℝ²`, the datum is a cylinder test function, `u` is the
Duhamel (Picard-class) solution and satisfies the equation. -/
structure FwdData (c ν T : ℝ) (w : ℝ → Pl → UnforcedLeray.Train.Vec) (f : Pl → ℝ)
    (u : ℝ → Pl → ℝ) : Prop where
  hc : 0 < c
  hν : 0 < ν
  hT : 0 ≤ T
  coeff : CylCoeff c T w
  smooth : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : ℝ × Pl => w z.1 z.2) (Icc 0 T ×ˢ univ)
  datum : B0579.IsCylTest c f
  mild : DuhamelSol c ν w 0 T f u
  pde : FwdPde ν T w u

/-- Local `C^k` on the band `band ρ`, uniformly for `σ ∈ [0, T]`: the slices are `C^k` there and
every iterated partial of order `≤ k` is jointly continuous and bounded on `[0, T] × band ρ`. -/
structure LocCk (T ρ : ℝ) (k : ℕ) (u : ℝ → Pl → ℝ) : Prop where
  slice : ∀ σ ∈ Icc 0 T, ContDiffOn ℝ k (u σ) (band ρ)
  cont : ∀ l : List (Fin 2), l.length ≤ k →
    ContinuousOn (fun z : ℝ × Pl => pdW l (u z.1) z.2) (Icc 0 T ×ˢ band ρ)
  bdd : ∀ l : List (Fin 2), l.length ≤ k →
    ∃ C : ℝ, ∀ σ ∈ Icc 0 T, ∀ x ∈ band ρ, |pdW l (u σ) x| ≤ C

/-- Spatial smoothness: `C^∞` slices whose iterated partials of every order are jointly continuous
on `[0, T] × ℝ²`. -/
structure SpSmooth (T : ℝ) (u : ℝ → Pl → ℝ) : Prop where
  slice : ∀ σ ∈ Icc 0 T, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (u σ)
  cont : ∀ l : List (Fin 2),
    ContinuousOn (fun z : ℝ × Pl => pdW l (u z.1) z.2) (Icc 0 T ×ˢ univ)

/-! ## The leaves -/

/-- **Leaf `T22/2/3/1/3`** (SP 2085-2093): for every `c > 0` the train velocity is a `CylCoeff`
drift on `[0, Σ/ν]` (`TrainCoeffBdd` of `Sub/T22_1/Plan.lean` with `1 ≤ c` relaxed to `0 < c`;
from `TcRegular` and `BwdDriftC2Bound`, both proved for every `c`). -/
def TrainCylCoeff : Prop :=
  ∀ (Sg ν c δ : ℝ), 0 < Sg → 0 < ν → 0 < c → 0 ≤ δ → ∀ tr : B0140.TrainSol ν c,
    TrainClose tr Sg δ → CylCoeff c (Sg / ν) tr.v

/-- **Leaf `T22/2/3/1/4`** (SP 2100-2105): the Picard class of `DuhamelSol` is `LocCk 2` on every
band (`PicClass.c2`, `cont0`, `cont1`, `cont2`, and `W2 · cosh ≤ B`). -/
def LocBase : Prop :=
  ∀ (c ν T : ℝ) (w : ℝ → Pl → UnforcedLeray.Train.Vec) (f : Pl → ℝ) (u : ℝ → Pl → ℝ),
    FwdData c ν T w f u → ∀ ρ : ℝ, LocCk T ρ 2 u

/-- **Leaf `T22/2/3/1/6`** (SP 2100-2105, local parabolic regularity with smooth drift): one order
of local regularity is gained on a band three units narrower.  Plan (organize task
`T22/2/3/1/6/org`): `η`-cutoffs `χ = 1` on `|η| ≤ ρ + 1`, `χ = 0` on `|η| ≥ ρ + 2`, and the
truncated drift `θ w` (`θ = 1` on `|η| ≤ ρ + 5/2`, all derivatives bounded); `χu` solves the
forward problem with drift `θ w` and a forcing supported in `ρ + 1 ≤ |η| ≤ ρ + 2`; a classical
bounded solution satisfies Duhamel; the Picard fixed point in the class
`{Z ∈ C^k_b : χ₂ Z ∈ C^{k+1}_b}` (`χ₂ = 1` on `|η| ≤ ρ`, `0` on `|η| ≥ ρ + 1/2`) exists by the
commutator gain of `[χ₂, ∫H]` and the off-diagonal smoothness of the heat kernel, and equals `χu`
by uniqueness in `C²`. -/
def LocStep : Prop :=
  ∀ (c ν T : ℝ) (w : ℝ → Pl → UnforcedLeray.Train.Vec) (f : Pl → ℝ) (u : ℝ → Pl → ℝ),
    FwdData c ν T w f u → ∀ k : ℕ, 2 ≤ k → ∀ ρ : ℝ, LocCk T (ρ + 3) k u → LocCk T ρ (k + 1) u

/-- **Leaf `T22/2/3/1/5`**: local regularity of every order on every band gives spatial
smoothness (the bands are open and cover the plane). -/
def LocAssemble : Prop :=
  ∀ (T : ℝ) (u : ℝ → Pl → ℝ), (∀ k : ℕ, 2 ≤ k → ∀ ρ : ℝ, LocCk T ρ k u) → SpSmooth T u

/-- **Leaf `T22/2/3/1/7`** (SP 2100-2105, time regularity from the equation): with a jointly
smooth drift, a spatially smooth solution of the forward equation is jointly `C^∞` on
`[0, T] × ℝ²`.  Plan (organize task `T22/2/3/1/7/org`): `∂_σ ∂^α u = ∂^α(νΔu - w·∇u)` (FTC in `σ`
and differentiation under the integral in `x`); the class generated by `u` under spatial
partials, sums and products with jointly smooth coefficients is closed under `∂_σ`; continuous
mixed partials of every order give `ContDiffOn` (`contDiffOn_succ_iff_fderivWithin`; the case
`T = 0` separately). -/
def FwdJointSmooth : Prop :=
  ∀ (ν T : ℝ) (w : ℝ → Pl → UnforcedLeray.Train.Vec) (u : ℝ → Pl → ℝ), 0 ≤ T →
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : ℝ × Pl => w z.1 z.2) (Icc 0 T ×ˢ univ) →
    SpSmooth T u → FwdPde ν T w u →
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : ℝ × Pl => u z.1 z.2) (Icc 0 T ×ˢ univ)

/-! ## Proved steps -/

/-- The local induction: `LocCk k` on every band for every `k ≥ 2`. -/
theorem locCk_all (h0 : LocBase) (h1 : LocStep) {c ν T : ℝ}
    {w : ℝ → Pl → UnforcedLeray.Train.Vec} {f : Pl → ℝ} {u : ℝ → Pl → ℝ}
    (hd : FwdData c ν T w f u) : ∀ k : ℕ, 2 ≤ k → ∀ ρ : ℝ, LocCk T ρ k u := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => exact h0 c ν T w f u hd
  | succ k hk ih => exact fun ρ => h1 c ν T w f u hd k hk ρ (ih (ρ + 3))

/-- Spatial smoothness of the forward solution from the three local leaves. -/
theorem spSmooth_of (h0 : LocBase) (h1 : LocStep) (h2 : LocAssemble) {c ν T : ℝ}
    {w : ℝ → Pl → UnforcedLeray.Train.Vec} {f : Pl → ℝ} {u : ℝ → Pl → ℝ}
    (hd : FwdData c ν T w f u) : SpSmooth T u :=
  h2 T u (locCk_all h0 h1 hd)

/-- The affine time reversal `(σ, x) ↦ (t - σ, x)`. -/
theorem contDiff_rev (t : ℝ) {n : WithTop ℕ∞} :
    ContDiff ℝ n (fun z : ℝ × Pl => (t - z.1, z.2)) :=
  (contDiff_const.sub contDiff_fst).prodMk contDiff_snd

/-- `CylCoeff` passes to the reversed drift on `[0, t - s]` when `[s, t] ⊆ [0, T]`. -/
theorem cylCoeff_revDrift {c T : ℝ} {v : ℝ → Pl → UnforcedLeray.Train.Vec} (hv : CylCoeff c T v)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ T) : CylCoeff c (t - s) (revDrift t v) := by
  have hmem : ∀ σ ∈ Icc (0 : ℝ) (t - s), t - σ ∈ Icc (0 : ℝ) T := fun σ hσ =>
    ⟨by linarith [hσ.2], by linarith [hσ.1]⟩
  have hmaps : MapsTo (fun z : ℝ × Pl => (t - z.1, z.2)) (Icc 0 (t - s) ×ˢ univ)
      (Icc 0 T ×ˢ univ) := fun z hz => ⟨hmem z.1 hz.1, mem_univ _⟩
  have hfd : ∀ σ : ℝ, ∀ x : Pl,
      fderiv ℝ (revDrift t v σ) x = -fderiv ℝ (v (t - σ)) x := fun σ x => by
    show fderiv ℝ (fun y => -v (t - σ) y) x = _
    exact fderiv_fun_neg
  obtain ⟨M, hM⟩ := hv.bdd
  obtain ⟨M', hM'⟩ := hv.dbdd
  refine ⟨fun σ hσ => (hv.slice (t - σ) (hmem σ hσ)).neg, ?_, ?_, ?_, ⟨M, ?_⟩, ⟨M', ?_⟩⟩
  · exact (hv.cont.comp (contDiff_rev t (n := 0)).continuous.continuousOn hmaps).neg
  · have h := (hv.dcont.comp (contDiff_rev t (n := 0)).continuous.continuousOn hmaps).neg
    exact h.congr fun z _ => hfd z.1 z.2
  · intro σ hσ x
    show -v (t - σ) (x.1 + c, x.2) = -v (t - σ) x
    rw [hv.periodic (t - σ) (hmem σ hσ) x]
  · intro σ hσ x
    show ‖-v (t - σ) x‖ ≤ M
    rw [norm_neg]
    exact hM (t - σ) (hmem σ hσ) x
  · intro σ hσ x
    rw [hfd, norm_neg]
    exact hM' (t - σ) (hmem σ hσ) x

/-- The reversed train drift is jointly `C^∞` on `[0, t - s] × ℝ²` (`IsTrain.smooth_v`). -/
theorem revDrift_smooth {ν c : ℝ} (tr : B0140.TrainSol ν c) {s t : ℝ} (hs : 0 ≤ s) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : ℝ × Pl => revDrift t tr.v z.1 z.2)
      (Icc 0 (t - s) ×ˢ univ) := by
  have hmaps : MapsTo (fun z : ℝ × Pl => (t - z.1, z.2)) (Icc 0 (t - s) ×ˢ univ)
      (Ici 0 ×ˢ univ) := fun z hz => ⟨show (0 : ℝ) ≤ t - z.1 by linarith [hz.1.2], mem_univ _⟩
  exact (tr.isTrain.smooth_v.comp (contDiff_rev t).contDiffOn hmaps).neg

/-- `|g x| ≤ W2 g x`. -/
theorem abs_le_W2 (g : Pl → ℝ) (x : Pl) : |g x| ≤ W2 g x := by
  unfold W2
  have := abs_nonneg (B0579.pd 0 g x)
  have := abs_nonneg (B0579.pd 1 g x)
  have := abs_nonneg (B0579.pd 0 (B0579.pd 0 g) x)
  have := abs_nonneg (B0579.pd 0 (B0579.pd 1 g) x)
  have := abs_nonneg (B0579.pd 1 (B0579.pd 0 g) x)
  have := abs_nonneg (B0579.pd 1 (B0579.pd 1 g) x)
  linarith

/-! ## The assembly -/

/-- **`BwdExists` from the route.**  Time reversal of the forward Duhamel solution with the
reversed drift; the terminal value, periodicity, boundedness and the backward equation come from
the Picard class and `DuhamelToPde`, the joint smoothness from the regularity leaves. -/
theorem bwdExists_of_route (hA : TrainCylCoeff) (hB : DuhamelExists) (hC : DuhamelToPde)
    (hD : LocBase) (hE : LocStep) (hF : LocAssemble) (hG : FwdJointSmooth) : BwdExists := by
  intro Sg ν c δ hSg hν hc hδ tr htr s t hs hst ht ψ hψ
  have hT : (0 : ℝ) ≤ t - s := by linarith
  set w := revDrift t tr.v with hw_def
  have hcoef : CylCoeff c (t - s) w := cylCoeff_revDrift (hA Sg ν c δ hSg hν hc hδ tr htr) hs hst ht
  have hws := revDrift_smooth tr (t := t) hs
  obtain ⟨u, hu⟩ := hB c ν 0 (t - s) w hc hν le_rfl hT hcoef ψ hψ
  have hpde : FwdPde ν (t - s) w u := hC c ν 0 (t - s) w hc hν le_rfl hT hcoef ψ hψ u hu
  have hd : FwdData c ν (t - s) w ψ u := ⟨hc, hν, hT, hcoef, hws, hψ, hu, hpde⟩
  have hsm := hG ν (t - s) w u hT hws (spSmooth_of hD hE hF hd) hpde
  obtain ⟨B, hB'⟩ := hu.cls
  have hmem : ∀ r ∈ Icc s t, t - r ∈ Icc (0 : ℝ) (t - s) := fun r hr =>
    ⟨by linarith [hr.2], by linarith [hr.1]⟩
  refine ⟨fun r => u (t - r), ?_, ?_, ?_, ⟨B, ?_⟩, ?_⟩
  · -- terminal value: `u 0 = ψ` from the Duhamel identity at `σ = 0`
    show u (t - t) = ψ
    rw [sub_self]
    funext x
    have h := hu.duhamel 0 ⟨le_rfl, hT⟩ x
    simp only [duhamelMap, duhamelConv, heatSG, sub_self, mul_zero, le_refl, ↓reduceIte,
      intervalIntegral.integral_same, sub_zero] at h
    exact h
  · -- joint smoothness: composition with the time reversal
    have hmaps : MapsTo (fun z : ℝ × Pl => (t - z.1, z.2)) (Icc s t ×ˢ univ)
        (Icc 0 (t - s) ×ˢ univ) := fun z hz => ⟨hmem z.1 hz.1, mem_univ _⟩
    exact hsm.comp (contDiff_rev t).contDiffOn hmaps
  · intro r hr x
    exact hB'.periodic (t - r) (hmem r hr) x
  · intro r hr x
    have hb := hB'.bound (t - r) (hmem r hr) x
    have h0 : 0 ≤ W2 (u (t - r)) x := le_trans (abs_nonneg _) (abs_le_W2 _ _)
    calc |u (t - r) x| ≤ W2 (u (t - r)) x := abs_le_W2 _ _
      _ ≤ W2 (u (t - r)) x * Real.cosh x.2 := le_mul_of_one_le_right h0 (Real.one_le_cosh _)
      _ ≤ B := hb
  · intro r hr x
    have hσ : t - r ∈ Ioo (0 : ℝ) (t - s) := ⟨by linarith [hr.2], by linarith [hr.1]⟩
    have h1 := (hpde (t - r) (Ioo_subset_Icc_self hσ) x).hasDerivAt (Icc_mem_nhds hσ.1 hσ.2)
    have h2 : HasDerivAt (fun r' : ℝ => t - r') (-1) r := (hasDerivAt_id' r).const_sub t
    have h3 := HasDerivAt.comp r h1 h2
    have e : ∀ i : Fin 2, w (t - r) x i = -tr.v r x i := fun i => by
      simp only [hw_def, revDrift, sub_sub_cancel, PiLp.neg_apply]
    have h4 : (ν * lapP (u (t - r)) x - (w (t - r) x 0 * B0579.pd 0 (u (t - r)) x +
        w (t - r) x 1 * B0579.pd 1 (u (t - r)) x)) * -1 =
        -(ν * lapP (u (t - r)) x + (tr.v r x 0 * B0579.pd 0 (u (t - r)) x +
          tr.v r x 1 * B0579.pd 1 (u (t - r)) x)) := by
      rw [e 0, e 1]
      ring
    exact h3.congr_deriv h4

end BwdRoute

end UnforcedLeray.Short.IIb
