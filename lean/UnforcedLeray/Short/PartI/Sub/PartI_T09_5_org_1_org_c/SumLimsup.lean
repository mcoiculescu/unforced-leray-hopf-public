import UnforcedLeray.Short.PartI.Sub.PartI_T09_5_org_1_org_c.JetSum
import UnforcedLeray.Short.PartI.Tasks.ClassicalOdd.EtaCutoffFacts
import UnforcedLeray.Short.PartI.Tasks.ClassicalOdd.ClassicalEnergyBound
import UnforcedLeray.Short.PartI.Tasks.ClassicalOdd.SlicePoisson
import UnforcedLeray.Short.PartI.Tasks.ClassicalOdd.VelocityDecayOfEnergy
import UnforcedLeray.Short.PartI.Tasks.ClassicalOdd.CylinderPoissonBound
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.ErrJetL2.VelocityJetL2.CutoffL2OfBound
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.ErrJetL2.VelocityJetL2.EnergyIneq
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.ErrJetL2.VelocityJetL2.EnergyIneq.ConsAppend
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.ForcingIBP

/-!
# `PartI:T09/5/org/1/org/c/1`: decomposition of `TrainJetSumLimsup`

Source: `the November 2 reference manuscript`,
lines 270-288: the BUC solution "is also the finite-energy solution ... which continues `L²`
membership.  Approximation and transverse cutoffs then give the velocity and vorticity energy
identities."

Target (`JetSum.lean`): for a BUC train, `limsup_{s→0+} S_j(s) ≤ S_j(0)`, where
`S_j(s) = ∫_cell Σ_{|w| ≤ j} Σ_k (∂_w v_k(s))²` (`trainJetSum`).

## Route

* **Order `0`** (the velocity energy identity with transverse cutoffs, lines 283-285).  The proved
  leaves of `ClassicalEnergyBound` (`Sub/T02_3_10.lean`, `Tasks/ClassicalOdd/ClassicalEnergyBound`)
  give, for the classical train on `[0, 1]` with its bounded pressure (`classicalPressureBound_of`),
  `∫_cell |v(s)|² ≤ ∫_cell |v(0)|² + K s` (`tjsl_classicalEnergyGrowth_of`: the proof of
  `classicalEnergyBound_of`, keeping the linear growth instead of bounding it).  So
  `limsup_{s→0+} S_0(s) ≤ S_0(0)`.  (This replaces the mild `L²` inequality of lines 277-280
  suggested by the organizer spec: the cutoff energy route of lines 283-285 is already proved for
  classical solutions, while the mild inequality would need the Duhamel formula of the train.)
* **Order `≥ 1`.**  Splitting each word of length `≥ 1` as `b :: u` (`tjsl_sum_wordsUpTo_succ`),
  `S_{j+1}(s) = S_0(s) + Σ_{|u| ≤ j} ∫_cell |∇ ∂_u v(s)|²`, and for the divergence-free field
  `g = ∂_u v(s)` the exact identity `∫_cell |∇g|² = ∫_cell (curl g)²` (`CurlGradIdentity`) with
  `curl g = ∂_u ω(s)` (`DerivWordConsAppend`) gives `S_{j+1}(s) = S_0(s) + Ω_j(s)`,
  `Ω_j(s) = ∫_cell Σ_{|u| ≤ j} (∂_u ω(s))²` (`tjsl_trainJetSum_succ`).
* **Vorticity jets.**  `VortJetEnergyIneq` (proved, `F_R' ≤ C F_R + C` uniformly in `R ≥ 1`) and the
  sharp Gronwall bound `F_R(s) + 1 ≤ (F_R(0) + 1) e^{Cs}` (`tjsl_gronwall_sharp`) give
  `F_R(s) ≤ (Ω_j(0) + 1) e^{Cs} - 1` for all `R`; `CutoffL2OfBound` and `EbLimit` (monotone and
  dominated convergence, `R → ∞`) give `Ω_j(s) ≤ (Ω_j(0) + 1) e^{Cs} - 1`, so
  `limsup_{s→0+} Ω_j(s) ≤ Ω_j(0)` (`tjsl_vort_upper`).

`CurlGradIdentity` is derived here (`curlGradIdentity_of`) from the two leaves `CurlGradCutoff`
(the cutoff integration by parts) and `CutoffErrorLimit` (the limit `R → ∞`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec)

/-! ### The leaves -/

/-- **Leaf (the cutoff curl-gradient identity)** (lines 283-286, "transverse cutoffs then give the
velocity and vorticity energy identities").  For smooth `c`-periodic `g = (g₀, g₁)` with
`∂_q g₀ + ∂_η g₁ = 0` and every `R ≥ 1`, with `χ_R = etaCutoff R`:
`∫_cell χ_R |∇g|² = ∫_cell χ_R (∂_q g₁ - ∂_η g₀)² - 2 ∫_cell χ_R'(η) g₀ ∂_q g₁`.
(Pointwise, `div g = 0` gives `|∇g|² - (curl g)² = -2 det ∇g` and
`det ∇g = ∂_q(g₀ ∂_η g₁) - ∂_η(g₀ ∂_q g₁)`; the `q`-derivative integrates to `0` by periodicity and
the `η`-derivative leaves `-∫ χ_R' g₀ ∂_q g₁`, by `CellDerivZero` applied to `χ_R g₀ ∂_η g₁` and
`χ_R g₀ ∂_q g₁`, which vanish for `|η| ≥ 2R`.) -/
def CurlGradCutoff : Prop :=
  ∀ (c : ℝ) (g₀ g₁ : Plane → ℝ), 0 < c → ContDiff ℝ ∞ g₀ → ContDiff ℝ ∞ g₁ →
    Cyl.IsPeriodic c g₀ → Cyl.IsPeriodic c g₁ →
    (∀ z : Plane, Cyl.partialQ g₀ z + Cyl.partialEta g₁ z = 0) →
    ∀ R : ℝ, 1 ≤ R →
      ∫ z in Cyl.cell c, etaCutoff R z.2 * ((Cyl.partialQ g₀ z) ^ 2 + (Cyl.partialQ g₁ z) ^ 2 +
          ((Cyl.partialEta g₀ z) ^ 2 + (Cyl.partialEta g₁ z) ^ 2)) =
        (∫ z in Cyl.cell c, etaCutoff R z.2 * (Cyl.partialQ g₁ z - Cyl.partialEta g₀ z) ^ 2) -
          2 * ∫ z in Cyl.cell c, deriv (etaCutoff R) z.2 * (g₀ z * Cyl.partialQ g₁ z)

/-- **Leaf (`R → ∞` in a cutoff identity with a boundary error)** (real analysis; lines 283-286,
the transverse cutoffs).  Let `F, G, a, b` be continuous on the plane with `0 ≤ G ≤ 2F`,
`b² ≤ F`, `|a|, |b| ≤ M`, and for every `R ≥ 1`
`∫_cell χ_R F = ∫_cell χ_R G - 2 ∫_cell χ_R'(η) a b`.  Then `∫_cell F = ∫_cell G` (as
`lintegral`s, both possibly `⊤`).  (The error is `O(1)` uniformly in `R`
(`EbStripBound`, `|ab| ≤ M²`), so `∫ F = ⊤` forces `∫ G = ⊤` and conversely (`G ≤ 2F`); if
`∫ F < ⊤`, Young's inequality `|b| ≤ (√R b² + 1/√R)/2` on the support `|η| ≤ 2R` of `χ_R'`
(measure `≤ 4cR`, `|χ_R'| ≤ C₀/R`, `EtaCutoffFacts`) gives error `≤ C₀ M (∫F + 4c)/√R → 0`, and
dominated convergence (`tendsto_cutoff_integral`, `Sub/PartI_T04_5.lean`) passes to the limit.) -/
def CutoffErrorLimit : Prop :=
  ∀ (c M : ℝ) (F G a b : Plane → ℝ), 0 < c → Continuous F → Continuous G → Continuous a →
    Continuous b → (∀ z, 0 ≤ G z) → (∀ z, G z ≤ 2 * F z) → (∀ z, b z ^ 2 ≤ F z) →
    (∀ z, |a z| ≤ M ∧ |b z| ≤ M) →
    (∀ R : ℝ, 1 ≤ R → ∫ z in Cyl.cell c, etaCutoff R z.2 * F z =
      (∫ z in Cyl.cell c, etaCutoff R z.2 * G z) -
        2 * ∫ z in Cyl.cell c, deriv (etaCutoff R) z.2 * (a z * b z)) →
    ∫⁻ z in Cyl.cell c, ENNReal.ofReal (F z) = ∫⁻ z in Cyl.cell c, ENNReal.ofReal (G z)

/-- **The curl-gradient identity** (lines 283-286): for a smooth `c`-periodic divergence-free
`g = (g₀, g₁)` with `g` and `∇g` bounded, `∫_cell |∇g|² = ∫_cell (curl g)²` (`lintegral`s).
Derived from `CurlGradCutoff` and `CutoffErrorLimit` (`curlGradIdentity_of`). -/
def CurlGradIdentity : Prop :=
  ∀ (c : ℝ) (g₀ g₁ : Plane → ℝ), 0 < c → ContDiff ℝ ∞ g₀ → ContDiff ℝ ∞ g₁ →
    Cyl.IsPeriodic c g₀ → Cyl.IsPeriodic c g₁ →
    (∀ z : Plane, Cyl.partialQ g₀ z + Cyl.partialEta g₁ z = 0) →
    (∃ M : ℝ, ∀ z : Plane, |g₀ z| ≤ M ∧ |g₁ z| ≤ M ∧ |Cyl.partialQ g₀ z| ≤ M ∧
      |Cyl.partialEta g₀ z| ≤ M ∧ |Cyl.partialQ g₁ z| ≤ M ∧ |Cyl.partialEta g₁ z| ≤ M) →
    ∫⁻ z in Cyl.cell c, ENNReal.ofReal ((Cyl.partialQ g₀ z) ^ 2 + (Cyl.partialQ g₁ z) ^ 2 +
        ((Cyl.partialEta g₀ z) ^ 2 + (Cyl.partialEta g₁ z) ^ 2)) =
      ∫⁻ z in Cyl.cell c, ENNReal.ofReal ((Cyl.partialQ g₁ z - Cyl.partialEta g₀ z) ^ 2)

theorem curlGradIdentity_of (h1 : CurlGradCutoff) (h2 : CutoffErrorLimit) : CurlGradIdentity := by
  intro c g₀ g₁ hc hg₀ hg₁ hp₀ hp₁ hdiv hb
  obtain ⟨M, hM⟩ := hb
  have hQ₀ : Continuous (Cyl.partialQ g₀) := (B0151.contDiff_partialX_infty hg₀).continuous
  have hQ₁ : Continuous (Cyl.partialQ g₁) := (B0151.contDiff_partialX_infty hg₁).continuous
  have hE₀ : Continuous (Cyl.partialEta g₀) := (B0151.contDiff_partialY_infty hg₀).continuous
  have hE₁ : Continuous (Cyl.partialEta g₁) := (B0151.contDiff_partialY_infty hg₁).continuous
  refine h2 c M
    (fun z => (Cyl.partialQ g₀ z) ^ 2 + (Cyl.partialQ g₁ z) ^ 2 +
      ((Cyl.partialEta g₀ z) ^ 2 + (Cyl.partialEta g₁ z) ^ 2))
    (fun z => (Cyl.partialQ g₁ z - Cyl.partialEta g₀ z) ^ 2) g₀ (Cyl.partialQ g₁) hc
    (by fun_prop) (by fun_prop) hg₀.continuous hQ₁ (fun z => sq_nonneg _) (fun z => ?_)
    (fun z => ?_) (fun z => ⟨(hM z).1, (hM z).2.2.2.2.1⟩)
    (fun R hR => h1 c g₀ g₁ hc hg₀ hg₁ hp₀ hp₁ hdiv R hR)
  · nlinarith [sq_nonneg (Cyl.partialQ g₁ z + Cyl.partialEta g₀ z), sq_nonneg (Cyl.partialQ g₀ z),
      sq_nonneg (Cyl.partialEta g₁ z)]
  · nlinarith [sq_nonneg (Cyl.partialQ g₀ z), sq_nonneg (Cyl.partialEta g₀ z),
      sq_nonneg (Cyl.partialEta g₁ z)]

/-! ### Real analysis helpers -/

/-- Upper bounds by a function with a limit bound the `limsup` along `s → 0+`. -/
theorem tjsl_limsup_le {f g : ℝ → ℝ≥0∞} {a : ℝ≥0∞}
    (hle : ∀ᶠ s in nhdsWithin (0 : ℝ) (Ici 0), f s ≤ g s)
    (hg : Tendsto g (nhdsWithin (0 : ℝ) (Ici 0)) (𝓝 a)) :
    limsup f (nhdsWithin (0 : ℝ) (Ici 0)) ≤ a :=
  (limsup_le_limsup hle).trans hg.limsup_eq.le

/-- **Sharp Gronwall** (the proof of `cutoffGronwall_proof`, keeping `F(s) + 1`). -/
theorem tjsl_gronwall_sharp (F : ℝ → ℝ) (S C : ℝ) (hS : 0 < S) (hcont : ContinuousOn F (Icc 0 S))
    (hder : ∀ s ∈ Ioo (0 : ℝ) S, ∃ D : ℝ, HasDerivAt F D s ∧ D ≤ C * F s + C) :
    ∀ s ∈ Icc (0 : ℝ) S, F s + 1 ≤ (F 0 + 1) * Real.exp (C * s) := by
  intro s hs
  have hEc : Continuous (fun t : ℝ => Real.exp (-(C * t))) :=
    Real.continuous_exp.comp ((continuous_const.mul continuous_id).neg)
  have hGc : ContinuousOn (fun t => (F t + 1) * Real.exp (-(C * t))) (Icc 0 S) :=
    (hcont.add continuousOn_const).mul hEc.continuousOn
  have hGd : ∀ t ∈ Ioo (0 : ℝ) S, ∃ D : ℝ,
      HasDerivAt (fun t => (F t + 1) * Real.exp (-(C * t))) D t ∧ D ≤ 0 := by
    intro t ht
    obtain ⟨D, hD, hDle⟩ := hder t ht
    have he : HasDerivAt (fun t : ℝ => Real.exp (-(C * t))) (Real.exp (-(C * t)) * -(C * 1)) t :=
      ((hasDerivAt_id' t).const_mul C).neg.exp
    refine ⟨D * Real.exp (-(C * t)) + (F t + 1) * (Real.exp (-(C * t)) * -(C * 1)),
      (hD.add_const 1).mul he, ?_⟩
    have hpos := Real.exp_pos (-(C * t))
    have e : D * Real.exp (-(C * t)) + (F t + 1) * (Real.exp (-(C * t)) * -(C * 1)) =
        (D - (C * F t + C)) * Real.exp (-(C * t)) := by ring
    rw [e]
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith) hpos.le
  have hanti : AntitoneOn (fun t => (F t + 1) * Real.exp (-(C * t))) (Icc 0 S) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 S) hGc
    · rw [interior_Icc]
      intro t ht
      obtain ⟨D, hD, _⟩ := hGd t ht
      exact hD.differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro t ht
      obtain ⟨D, hD, hle⟩ := hGd t ht
      rw [hD.deriv]
      exact hle
  have h0 : (0 : ℝ) ∈ Icc 0 S := ⟨le_rfl, hS.le⟩
  have hGs := hanti h0 hs hs.1
  simp only [mul_zero, neg_zero, Real.exp_zero, mul_one] at hGs
  have hpos : 0 < Real.exp (C * s) := Real.exp_pos _
  have e : Real.exp (-(C * s)) * Real.exp (C * s) = 1 := by
    rw [← Real.exp_add]
    simp
  calc F s + 1 = (F s + 1) * Real.exp (-(C * s)) * Real.exp (C * s) := by
        rw [mul_assoc, e, mul_one]
    _ ≤ (F 0 + 1) * Real.exp (C * s) := mul_le_mul_of_nonneg_right hGs hpos.le

/-! ### Words of length at most `j + 1` -/

theorem tjsl_wordsUpTo_zero : wordsUpTo 0 = {[]} := by
  ext u
  rw [mem_wordsUpTo, Finset.mem_singleton]
  constructor
  · intro h
    rcases u with _ | ⟨a, l⟩
    · rfl
    · simp only [List.length_cons] at h
      omega
  · rintro rfl
    simp

theorem tjsl_sum_wordsUpTo_succ {M : Type*} [AddCommMonoid M] (φ : List Bool → M) (j : ℕ) :
    ∑ w ∈ wordsUpTo (j + 1), φ w =
      φ [] + ∑ u ∈ wordsUpTo j, (φ (true :: u) + φ (false :: u)) := by
  have hset : wordsUpTo (j + 1) = insert []
      ((wordsUpTo j).image (List.cons true) ∪ (wordsUpTo j).image (List.cons false)) := by
    ext w
    simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_image, mem_wordsUpTo]
    constructor
    · intro h
      rcases w with _ | ⟨b, u⟩
      · exact Or.inl rfl
      · right
        have hu : u.length ≤ j := by
          simp only [List.length_cons] at h
          omega
        cases b
        · exact Or.inr ⟨u, hu, rfl⟩
        · exact Or.inl ⟨u, hu, rfl⟩
    · rintro (rfl | ⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩)
      · simp
      · simp only [List.length_cons]
        omega
      · simp only [List.length_cons]
        omega
  have hdisj : Disjoint ((wordsUpTo j).image (List.cons true))
      ((wordsUpTo j).image (List.cons false)) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    obtain ⟨u, -, rfl⟩ := Finset.mem_image.1 ha
    obtain ⟨u', -, h⟩ := Finset.mem_image.1 hb
    simp at h
  have hnot : [] ∉ (wordsUpTo j).image (List.cons true) ∪
      (wordsUpTo j).image (List.cons false) := by
    simp
  rw [hset, Finset.sum_insert hnot, Finset.sum_union hdisj,
    Finset.sum_image List.cons_injective.injOn, Finset.sum_image List.cons_injective.injOn,
    ← Finset.sum_add_distrib]

/-- Splitting the `lintegral` of a sum over the words of length `≤ j + 1`. -/
theorem tjsl_lintegral_split {μ : Measure Plane} (f : List Bool → Plane → ℝ)
    (hf : ∀ w, Continuous (f w)) (hnn : ∀ w z, 0 ≤ f w z) (j : ℕ) :
    ∫⁻ z, ENNReal.ofReal (∑ w ∈ wordsUpTo (j + 1), f w z) ∂μ =
      ∫⁻ z, ENNReal.ofReal (f [] z) ∂μ +
        ∑ u ∈ wordsUpTo j, ∫⁻ z, ENNReal.ofReal (f (true :: u) z + f (false :: u) z) ∂μ := by
  have hpt : ∀ z, ENNReal.ofReal (∑ w ∈ wordsUpTo (j + 1), f w z) =
      ENNReal.ofReal (f [] z) +
        ∑ u ∈ wordsUpTo j, ENNReal.ofReal (f (true :: u) z + f (false :: u) z) := by
    intro z
    rw [tjsl_sum_wordsUpTo_succ (fun w => f w z) j,
      ENNReal.ofReal_add (hnn [] z) (Finset.sum_nonneg fun u _ => add_nonneg (hnn _ z) (hnn _ z)),
      ENNReal.ofReal_sum_of_nonneg (fun u _ => add_nonneg (hnn _ z) (hnn _ z))]
  calc ∫⁻ z, ENNReal.ofReal (∑ w ∈ wordsUpTo (j + 1), f w z) ∂μ
      = ∫⁻ z, (ENNReal.ofReal (f [] z) +
          ∑ u ∈ wordsUpTo j, ENNReal.ofReal (f (true :: u) z + f (false :: u) z)) ∂μ :=
        lintegral_congr hpt
    _ = ∫⁻ z, ENNReal.ofReal (f [] z) ∂μ +
          ∫⁻ z, ∑ u ∈ wordsUpTo j, ENNReal.ofReal (f (true :: u) z + f (false :: u) z) ∂μ :=
        lintegral_add_left (hf []).measurable.ennreal_ofReal _
    _ = _ := by
        congr 1
        exact lintegral_finsetSum _
          (fun u _ => ((hf (true :: u)).add (hf (false :: u))).measurable.ennreal_ofReal)

theorem tjsl_derivWord_zero :
    ∀ w : List Bool, B0151.derivWord w (fun _ : Plane => (0 : ℝ)) = fun _ => 0
  | [] => rfl
  | true :: w => by
      show GaussianVortex.partialX (B0151.derivWord w (fun _ : Plane => (0 : ℝ))) = fun _ => 0
      rw [tjsl_derivWord_zero w]
      funext z
      simp [GaussianVortex.partialX]
  | false :: w => by
      show GaussianVortex.partialY (B0151.derivWord w (fun _ : Plane => (0 : ℝ))) = fun _ => 0
      rw [tjsl_derivWord_zero w]
      funext z
      simp [GaussianVortex.partialY]

/-! ### Order `≥ 1`: the curl-gradient identity on the jets -/

/-- For `g = ∂_u v(s)`: `∫_cell |∇g|² = ∫_cell (∂_u ω(s))²`. -/
theorem tjsl_word_curlGrad (hCG : CurlGradIdentity) {ν c : ℝ} (hc : 0 < c)
    {tr : B0140.TrainSol ν c} (htr : IsBUCTrain tr) {s : ℝ} (hs : 0 ≤ s) (u : List Bool) :
    ∫⁻ z in Cyl.cell c, ENNReal.ofReal ((∑ k : Fin 2, (wordComp (true :: u) (tr.v s) k z) ^ 2) +
        ∑ k : Fin 2, (wordComp (false :: u) (tr.v s) k z) ^ 2) =
      ∫⁻ z in Cyl.cell c, ENNReal.ofReal ((vortWord tr u s z) ^ 2) := by
  have hg₀ : ContDiff ℝ ∞ (wordComp u (tr.v s) 0) :=
    B0151.contDiff_derivWord (vjl_slice_smooth tr hs 0) u
  have hg₁ : ContDiff ℝ ∞ (wordComp u (tr.v s) 1) :=
    B0151.contDiff_derivWord (vjl_slice_smooth tr hs 1) u
  have hQ0 : ContDiff ℝ ∞ (Cyl.partialQ (fun x => tr.v s x 0)) :=
    B0151.contDiff_derivWord (vjl_slice_smooth tr hs 0) [true]
  have hE1 : ContDiff ℝ ∞ (Cyl.partialEta (fun x => tr.v s x 1)) :=
    B0151.contDiff_derivWord (vjl_slice_smooth tr hs 1) [false]
  have hdiv : ∀ z : Plane,
      Cyl.partialQ (wordComp u (tr.v s) 0) z + Cyl.partialEta (wordComp u (tr.v s) 1) z = 0 := by
    intro z
    have hc0' := (ForcingIBP.derivWord_comm u (fun x => tr.v s x 0) (vjl_slice_smooth tr hs 0)).1
    have hc1' := (ForcingIBP.derivWord_comm u (fun x => tr.v s x 1) (vjl_slice_smooth tr hs 1)).2
    have hadd := ForcingIBP.derivWord_add_smooth u _ _ hQ0 hE1
    have hzero : (fun z => Cyl.partialQ (fun x => tr.v s x 0) z +
        Cyl.partialEta (fun x => tr.v s x 1) z) = fun _ => (0 : ℝ) :=
      funext fun z => tr.isTrain.solenoidal s hs z
    rw [hzero, tjsl_derivWord_zero] at hadd
    show Cyl.partialQ (B0151.derivWord u (fun x => tr.v s x 0)) z +
      Cyl.partialEta (B0151.derivWord u (fun x => tr.v s x 1)) z = 0
    rw [← hc0', ← hc1']
    exact (congrFun hadd z).symm
  have hsI : s ∈ Icc (0 : ℝ) s := ⟨hs, le_rfl⟩
  have hb : ∃ M : ℝ, ∀ z : Plane, |wordComp u (tr.v s) 0 z| ≤ M ∧
      |wordComp u (tr.v s) 1 z| ≤ M ∧ |Cyl.partialQ (wordComp u (tr.v s) 0) z| ≤ M ∧
      |Cyl.partialEta (wordComp u (tr.v s) 0) z| ≤ M ∧
      |Cyl.partialQ (wordComp u (tr.v s) 1) z| ≤ M ∧
      |Cyl.partialEta (wordComp u (tr.v s) 1) z| ≤ M := by
    obtain ⟨M1, hM1⟩ := vjl_wordBoundedOn htr hs u 0
    obtain ⟨M2, hM2⟩ := vjl_wordBoundedOn htr hs u 1
    obtain ⟨M3, hM3⟩ := vjl_wordBoundedOn htr hs (true :: u) 0
    obtain ⟨M4, hM4⟩ := vjl_wordBoundedOn htr hs (false :: u) 0
    obtain ⟨M5, hM5⟩ := vjl_wordBoundedOn htr hs (true :: u) 1
    obtain ⟨M6, hM6⟩ := vjl_wordBoundedOn htr hs (false :: u) 1
    have a1 := abs_nonneg M1
    have a2 := abs_nonneg M2
    have a3 := abs_nonneg M3
    have a4 := abs_nonneg M4
    have a5 := abs_nonneg M5
    have a6 := abs_nonneg M6
    refine ⟨|M1| + |M2| + |M3| + |M4| + |M5| + |M6|, fun z => ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
    · exact (hM1 s hsI z).trans (by linarith [le_abs_self M1])
    · exact (hM2 s hsI z).trans (by linarith [le_abs_self M2])
    · exact (hM3 s hsI z).trans (by linarith [le_abs_self M3])
    · exact (hM4 s hsI z).trans (by linarith [le_abs_self M4])
    · exact (hM5 s hsI z).trans (by linarith [le_abs_self M5])
    · exact (hM6 s hsI z).trans (by linarith [le_abs_self M6])
  have key := hCG c (wordComp u (tr.v s) 0) (wordComp u (tr.v s) 1) hc hg₀ hg₁
    (vjl_word_periodic tr hs u 0) (vjl_word_periodic tr hs u 1) hdiv hb
  have eR : ∀ z : Plane, vortWord tr u s z =
      Cyl.partialQ (wordComp u (tr.v s) 1) z - Cyl.partialEta (wordComp u (tr.v s) 0) z := by
    intro z
    rw [vortWord_eq tr hs u z]
    have a1 : wordComp (u ++ [true]) (tr.v s) 1 = wordComp (true :: u) (tr.v s) 1 :=
      (derivWordConsAppend_proof _ (vjl_slice_smooth tr hs 1) true u).symm
    have a0 : wordComp (u ++ [false]) (tr.v s) 0 = wordComp (false :: u) (tr.v s) 0 :=
      (derivWordConsAppend_proof _ (vjl_slice_smooth tr hs 0) false u).symm
    rw [a1, a0]
    rfl
  calc ∫⁻ z in Cyl.cell c, ENNReal.ofReal ((∑ k : Fin 2, (wordComp (true :: u) (tr.v s) k z) ^ 2) +
        ∑ k : Fin 2, (wordComp (false :: u) (tr.v s) k z) ^ 2)
      = ∫⁻ z in Cyl.cell c, ENNReal.ofReal ((Cyl.partialQ (wordComp u (tr.v s) 0) z) ^ 2 +
          (Cyl.partialQ (wordComp u (tr.v s) 1) z) ^ 2 +
          ((Cyl.partialEta (wordComp u (tr.v s) 0) z) ^ 2 +
            (Cyl.partialEta (wordComp u (tr.v s) 1) z) ^ 2)) := by
        refine lintegral_congr (fun z => ?_)
        simp only [Fin.sum_univ_two]
        rfl
    _ = ∫⁻ z in Cyl.cell c, ENNReal.ofReal
          ((Cyl.partialQ (wordComp u (tr.v s) 1) z - Cyl.partialEta (wordComp u (tr.v s) 0) z) ^ 2) :=
        key
    _ = ∫⁻ z in Cyl.cell c, ENNReal.ofReal ((vortWord tr u s z) ^ 2) := by
        refine lintegral_congr (fun z => ?_)
        rw [eR z]

/-- The summed vorticity jet energy `Ω_j(s) = ∫_cell Σ_{|u| ≤ j} (∂_u ω(s))²`. -/
def vortJetSum {ν c : ℝ} (tr : B0140.TrainSol ν c) (j : ℕ) (s : ℝ) : ℝ≥0∞ :=
  ∫⁻ z in Cyl.cell c, ENNReal.ofReal (∑ u ∈ wordsUpTo j, (vortWord tr u s z) ^ 2)

/-- `S_{j+1}(s) = S_0(s) + Ω_j(s)` for `s ≥ 0`. -/
theorem tjsl_trainJetSum_succ (hCG : CurlGradIdentity) {ν c : ℝ} (hc : 0 < c)
    {tr : B0140.TrainSol ν c} (htr : IsBUCTrain tr) {s : ℝ} (hs : 0 ≤ s) (j : ℕ) :
    trainJetSum tr (j + 1) s = trainJetSum tr 0 s + vortJetSum tr j s := by
  have hfc : ∀ w : List Bool, Continuous (fun z => ∑ k : Fin 2, (wordComp w (tr.v s) k z) ^ 2) :=
    fun w => continuous_finsetSum _ (fun k _ =>
      ((B0151.contDiff_derivWord (vjl_slice_smooth tr hs k) w).continuous).pow 2)
  have hsplit := tjsl_lintegral_split (μ := volume.restrict (Cyl.cell c))
    (fun w z => ∑ k : Fin 2, (wordComp w (tr.v s) k z) ^ 2) hfc
    (fun w z => Finset.sum_nonneg (fun k _ => sq_nonneg _)) j
  have h0 : trainJetSum tr 0 s =
      ∫⁻ z in Cyl.cell c, ENNReal.ofReal (∑ k : Fin 2, (wordComp [] (tr.v s) k z) ^ 2) := by
    unfold trainJetSum
    rw [tjsl_wordsUpTo_zero]
    simp only [Finset.sum_singleton]
  have hv : vortJetSum tr j s =
      ∑ u ∈ wordsUpTo j, ∫⁻ z in Cyl.cell c, ENNReal.ofReal ((vortWord tr u s z) ^ 2) := by
    unfold vortJetSum
    calc ∫⁻ z in Cyl.cell c, ENNReal.ofReal (∑ u ∈ wordsUpTo j, (vortWord tr u s z) ^ 2)
        = ∫⁻ z in Cyl.cell c, ∑ u ∈ wordsUpTo j, ENNReal.ofReal ((vortWord tr u s z) ^ 2) :=
          lintegral_congr (fun z => ENNReal.ofReal_sum_of_nonneg (fun u _ => sq_nonneg _))
      _ = ∑ u ∈ wordsUpTo j, ∫⁻ z in Cyl.cell c, ENNReal.ofReal ((vortWord tr u s z) ^ 2) :=
          lintegral_finsetSum _ (fun u _ =>
            ((vjl_vortWord_contDiff tr hs u).continuous.pow 2).measurable.ennreal_ofReal)
  rw [h0, hv]
  refine hsplit.trans (congrArg₂ (· + ·) rfl (Finset.sum_congr rfl (fun u _ => ?_)))
  exact tjsl_word_curlGrad hCG hc htr hs u

/-! ### Order `0`: the velocity energy -/

/-- `∫_cell |v(s)|² ≤ ∫_cell |v(0)|² + K s` on `[0, T]` for a classical solution with bounded
derivatives and bounded pressure: the proof of `classicalEnergyBound_of` (`Sub/T02_3_10.lean`),
keeping the linear growth. -/
theorem tjsl_classicalEnergyGrowth_of (hF : EtaCutoffFacts) (hC : EbContinuous) (hD : EbHasDeriv)
    (hE : EbDecomp) (hVi : EbViscousIdentity) (hTi : EbConvIdentity)
    (hPi : EbPressureIdentity) (hX : EbFluxBound) (hL : EbLimit)
    {ν c T Mp : ℝ} {v : ℝ → Plane → Vec} {p : ℝ → Plane → ℝ} (hν : 0 < ν) (hc : 1 ≤ c)
    (hcl : IsClassicalOn ν c T v p) (hb : HasBoundedDerivsOn T v)
    (hp : ∀ s ∈ Icc (0 : ℝ) T, ∀ z, |p s z| ≤ Mp) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ s ∈ Icc (0 : ℝ) T,
      ∫ z in Cyl.cell c, ‖v s z‖ ^ 2 ≤ (∫ z in Cyl.cell c, ‖v 0 z‖ ^ 2) + K * s := by
  have hc0 : 0 < c := by linarith
  obtain ⟨K, hK0, HK⟩ := hX ν c T Mp v p hν hc0 hcl hb hp
  obtain ⟨C₀, -, hFC⟩ := hF
  refine ⟨K, hK0, fun s hs => ?_⟩
  have hT0 : (0 : ℝ) ≤ T := hs.1.trans hs.2
  have hint0 : IntegrableOn (fun z => ‖v 0 z‖ ^ 2) (Cyl.cell c) :=
    hcl.finite_energy 0 ⟨le_rfl, hT0⟩
  refine hL c hc0 (fun z => ‖v s z‖ ^ 2) _ (fun z => sq_nonneg _) (hcl.finite_energy s hs) ?_
  intro R hR
  show ebEnergy c v R s ≤ _
  have hcont : ContinuousOn (ebEnergy c v R) (Icc 0 T) := hC ν c T v p hc0 hcl R hR
  have hle : ∀ r ∈ Ioo (0 : ℝ) T, ebDtIntegral c v R r ≤ K := by
    intro r hr
    have hr' : r ∈ Icc (0 : ℝ) T := Ioo_subset_Icc_self hr
    rw [hE ν c T v p hc0 hcl R hR r hr, hVi ν c T v p hc0 hcl R hR r hr',
      hTi ν c T v p hc0 hcl R hR r hr', hPi ν c T v p hc0 hcl R hR r hr']
    exact HK R hR r hr'
  set H : ℝ → ℝ := fun r => ebEnergy c v R r - K * r with hH
  have hHcont : ContinuousOn H (Icc 0 T) :=
    hcont.sub (continuousOn_const.mul continuousOn_id)
  have hHder : ∀ r ∈ Ioo (0 : ℝ) T, HasDerivAt H (ebDtIntegral c v R r - K) r := by
    intro r hr
    have h := (hD ν c T v p hc0 hcl R hR r hr).sub ((hasDerivAt_id' r).const_mul K)
    rwa [mul_one] at h
  have hanti : AntitoneOn H (Icc 0 T) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 T) hHcont
    · intro r hr
      rw [interior_Icc] at hr
      exact (hHder r hr).differentiableAt.differentiableWithinAt
    · intro r hr
      rw [interior_Icc] at hr
      rw [(hHder r hr).deriv]
      have := hle r hr
      linarith
  have hHs : H s ≤ H 0 := hanti ⟨le_rfl, hT0⟩ hs hs.1
  have hφ1 : ∀ z : Plane, etaCutoff R z.2 ≤ 1 := fun z => (hFC R hR).2.1 z.2 |>.2
  have h0 : ebEnergy c v R 0 ≤ ∫ z in Cyl.cell c, ‖v 0 z‖ ^ 2 := by
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun z => ?_) hint0
      (Filter.Eventually.of_forall fun z => ?_)
    · exact mul_nonneg (etaCutoff_nonneg R z.2) (sq_nonneg _)
    · have := mul_le_mul_of_nonneg_right (hφ1 z) (sq_nonneg ‖v 0 z‖)
      simpa using this
  have hH0 : H 0 = ebEnergy c v R 0 := by simp [hH]
  have hHs' : ebEnergy c v R s - K * s ≤ ebEnergy c v R 0 := by
    have := hHs
    rw [hH0] at this
    simpa [hH] using this
  linarith

/-- The energy of a BUC train grows at most linearly on `[0, 1]`. -/
theorem tjsl_trainEnergyGrowth {ν c : ℝ} (hν : 0 < ν) (hc : 1 ≤ c) {tr : B0140.TrainSol ν c}
    (htr : IsBUCTrain tr) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ s ∈ Icc (0 : ℝ) 1,
      ∫ z in Cyl.cell c, ‖tr.v s z‖ ^ 2 ≤ (∫ z in Cyl.cell c, ‖tr.v 0 z‖ ^ 2) + K * s := by
  obtain ⟨Mp, hMp⟩ := classicalPressureBound_of slicePoisson velocityDecayOfEnergy
    cylinderPoissonBound ν c 1 tr.v tr.p hν hc one_pos (trainSol_isClassicalOn tr 1)
    (htr 1 zero_le_one) (trainSol_pressureDecayOn tr 1)
  exact tjsl_classicalEnergyGrowth_of etaCutoffFacts (ebContinuous etaCutoffFacts)
    (ebHasDeriv etaCutoffFacts) (ebDecomp etaCutoffFacts ebSliceSmooth cellToolkit.1)
    (ebViscousIdentity etaCutoffFacts cellToolkit.1 cellToolkit.2 ebSliceSmooth)
    (ebConvIdentity etaCutoffFacts cellToolkit.1 cellToolkit.2 ebSliceSmooth)
    (ebPressureIdentity etaCutoffFacts cellToolkit.1 cellToolkit.2 ebSliceSmooth)
    (ebFluxBound (ebStripBound etaCutoffFacts) (ebDerivBounds ebSliceSmooth) ebSliceSmooth)
    (ebLimit etaCutoffFacts) hν hc (trainSol_isClassicalOn tr 1) (htr 1 zero_le_one)
    (fun s hs z => hMp s hs z)

theorem tjsl_trainJetSum_zero {ν c : ℝ} (tr : B0140.TrainSol ν c) {s : ℝ} (hs : 0 ≤ s) :
    trainJetSum tr 0 s = ENNReal.ofReal (∫ z in Cyl.cell c, ‖tr.v s z‖ ^ 2) := by
  have hint : IntegrableOn (fun z => ‖tr.v s z‖ ^ 2) (Cyl.cell c) := tr.isTrain.finite_energy s hs
  rw [ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun z => sq_nonneg _)]
  unfold trainJetSum
  refine lintegral_congr (fun z => ?_)
  rw [tjsl_wordsUpTo_zero, Finset.sum_singleton, EuclideanSpace.real_norm_sq_eq]
  rfl

/-- Order `0`: `S_0(s)` is bounded by a function tending to `S_0(0)` as `s → 0+`. -/
theorem tjsl_order0_upper {ν c : ℝ} (hν : 0 < ν) (hc : 1 ≤ c) {tr : B0140.TrainSol ν c}
    (htr : IsBUCTrain tr) :
    ∃ g : ℝ → ℝ≥0∞, Tendsto g (nhdsWithin (0 : ℝ) (Ici 0)) (𝓝 (trainJetSum tr 0 0)) ∧
      ∀ᶠ s in nhdsWithin (0 : ℝ) (Ici 0), trainJetSum tr 0 s ≤ g s := by
  obtain ⟨K, -, hK⟩ := tjsl_trainEnergyGrowth hν hc htr
  refine ⟨fun s => ENNReal.ofReal ((∫ z in Cyl.cell c, ‖tr.v 0 z‖ ^ 2) + K * s), ?_, ?_⟩
  · have hcont : Continuous (fun s : ℝ => (∫ z in Cyl.cell c, ‖tr.v 0 z‖ ^ 2) + K * s) := by
      fun_prop
    have hlim : ENNReal.ofReal ((∫ z in Cyl.cell c, ‖tr.v 0 z‖ ^ 2) + K * 0) =
        trainJetSum tr 0 0 := by
      rw [mul_zero, add_zero, tjsl_trainJetSum_zero tr le_rfl]
    rw [← hlim]
    exact (ENNReal.continuous_ofReal.tendsto _).comp
      ((hcont.tendsto 0).mono_left nhdsWithin_le_nhds)
  · filter_upwards [Icc_mem_nhdsGE (zero_lt_one' ℝ)] with s hs
    rw [tjsl_trainJetSum_zero tr hs.1]
    exact ENNReal.ofReal_le_ofReal (hK s hs)

/-! ### The vorticity jets -/

/-- `Ω_j(s)` is bounded by a function tending to `Ω_j(0)` as `s → 0+`. -/
theorem tjsl_vort_upper {ν c : ℝ} (hν : 0 < ν) (hc : 1 ≤ c) {tr : B0140.TrainSol ν c}
    (htr : IsBUCTrain tr) (j : ℕ) :
    ∃ g : ℝ → ℝ≥0∞, Tendsto g (nhdsWithin (0 : ℝ) (Ici 0)) (𝓝 (vortJetSum tr j 0)) ∧
      ∀ᶠ s in nhdsWithin (0 : ℝ) (Ici 0), vortJetSum tr j s ≤ g s := by
  by_cases htop : vortJetSum tr j 0 = ⊤
  · refine ⟨fun _ => ⊤, ?_, Filter.Eventually.of_forall fun s => le_top⟩
    rw [htop]
    exact tendsto_const_nhds
  have hc0 : 0 < c := by linarith
  obtain ⟨C, hC, hE⟩ := vortJetEnergyIneq_proof ν c hν hc tr htr j 1 one_pos
  obtain ⟨A, hA⟩ : ∃ A : ℝ, (vortJetSum tr j 0).toReal = A := ⟨_, rfl⟩
  refine ⟨fun s => ENNReal.ofReal ((A + 1) * Real.exp (C * s) - 1), ?_, ?_⟩
  · have hcont : Continuous (fun s : ℝ => (A + 1) * Real.exp (C * s) - 1) := by
      fun_prop
    have hlim : ENNReal.ofReal ((A + 1) * Real.exp (C * 0) - 1) = vortJetSum tr j 0 := by
      rw [mul_zero, Real.exp_zero, mul_one, add_sub_cancel_right, ← hA,
        ENNReal.ofReal_toReal htop]
    rw [← hlim]
    exact (ENNReal.continuous_ofReal.tendsto _).comp
      ((hcont.tendsto 0).mono_left nhdsWithin_le_nhds)
  · filter_upwards [Icc_mem_nhdsGE (zero_lt_one' ℝ)] with s hs
    have hg0nn : ∀ z, 0 ≤ ∑ u ∈ wordsUpTo j, vortWord tr u 0 z ^ 2 :=
      fun z => Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    have hg0c : Continuous (fun z => ∑ u ∈ wordsUpTo j, vortWord tr u 0 z ^ 2) :=
      continuous_finsetSum _ (fun u _ => (vjl_vortWord_contDiff tr le_rfl u).continuous.pow 2)
    have hF0 : ∀ R : ℝ, 1 ≤ R → vortJetEnergy tr j R 0 ≤ A := by
      intro R hR
      have hnn : 0 ≤ᵐ[volume.restrict (Cyl.cell c)]
          fun z => etaCutoff R z.2 * ∑ u ∈ wordsUpTo j, vortWord tr u 0 z ^ 2 :=
        Filter.Eventually.of_forall fun z => mul_nonneg (etaCutoff_nonneg R z.2) (hg0nn z)
      have hm : AEStronglyMeasurable
          (fun z => etaCutoff R z.2 * ∑ u ∈ wordsUpTo j, vortWord tr u 0 z ^ 2)
          (volume.restrict (Cyl.cell c)) :=
        ((cehd_eta_cont R).mul hg0c).aestronglyMeasurable
      unfold vortJetEnergy
      rw [integral_eq_lintegral_of_nonneg_ae hnn hm, ← hA]
      refine ENNReal.toReal_mono htop (lintegral_mono fun z => ENNReal.ofReal_le_ofReal ?_)
      exact mul_le_of_le_one_left (hg0nn z) (cehd_eta_le_one R z.2)
    have hFs : ∀ R : ℝ, 1 ≤ R → vortJetEnergy tr j R s ≤
        (A + 1) * Real.exp (C * s) - 1 := by
      intro R hR
      obtain ⟨hcont, hder⟩ := hE R hR
      have hG := tjsl_gronwall_sharp _ 1 C one_pos hcont hder s hs
      have hexp : 0 < Real.exp (C * s) := Real.exp_pos _
      have h1 := mul_le_mul_of_nonneg_right (add_le_add_right (hF0 R hR) 1) hexp.le
      linarith
    have hsc : Continuous (fun z => ∑ u ∈ wordsUpTo j, vortWord tr u s z ^ 2) :=
      continuous_finsetSum _ (fun u _ => (vjl_vortWord_contDiff tr hs.1 u).continuous.pow 2)
    have hmem : ∀ u ∈ wordsUpTo j, MemLp (vortWord tr u s) 2 (Cyl.cellμ c) := by
      intro u hu
      refine cutoffL2OfBound_proof c ((A + 1) * Real.exp (C * s) - 1)
        (vortWord tr u s) hc0 (vjl_vortWord_contDiff tr hs.1 u).continuous (fun R hR => ?_)
      refine le_trans ?_ (hFs R hR)
      have hR0 : 0 < R := by linarith
      unfold vortJetEnergy
      refine integral_mono (vjl_cutoff_integrable hR0
        ((vjl_vortWord_contDiff tr hs.1 u).continuous.pow 2)) (vjl_cutoff_integrable hR0 hsc)
        (fun z => ?_)
      exact mul_le_mul_of_nonneg_left (Finset.single_le_sum
        (f := fun u' => vortWord tr u' s z ^ 2) (fun _ _ => sq_nonneg _) hu)
        (etaCutoff_nonneg R z.2)
    have hint : IntegrableOn (fun z => ∑ u ∈ wordsUpTo j, vortWord tr u s z ^ 2) (Cyl.cell c) :=
      integrable_finsetSum _ (fun u hu => (hmem u hu).integrable_sq)
    have hle : ∫ z in Cyl.cell c, ∑ u ∈ wordsUpTo j, vortWord tr u s z ^ 2 ≤
        (A + 1) * Real.exp (C * s) - 1 :=
      ebLimit etaCutoffFacts c hc0 _ _ (fun z => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
        hint (fun R hR => hFs R hR)
    show ∫⁻ z in Cyl.cell c, ENNReal.ofReal (∑ u ∈ wordsUpTo j, (vortWord tr u s z) ^ 2) ≤ _
    rw [← ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun z => Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
    exact ENNReal.ofReal_le_ofReal hle

/-! ### The conditional theorem -/

/-- **`TrainJetSumLimsup` from the curl-gradient identity** (all other inputs are proved:
`ClassicalEnergyBound` leaves, `classicalPressureBound_of`, `VortJetEnergyIneq`,
`CutoffL2OfBound`, `EbLimit`, `DerivWordConsAppend`). -/
theorem trainJetSumLimsup_of (hCG : CurlGradIdentity) : TrainJetSumLimsup := by
  intro ν c hν hc tr htr j
  have hc0 : 0 < c := by linarith
  obtain ⟨g0, hg0, hle0⟩ := tjsl_order0_upper hν hc htr
  cases j with
  | zero => exact tjsl_limsup_le hle0 hg0
  | succ j =>
    obtain ⟨g1, hg1, hle1⟩ := tjsl_vort_upper hν hc htr j
    rw [tjsl_trainJetSum_succ hCG hc0 htr le_rfl j]
    refine tjsl_limsup_le ?_ (hg0.add hg1)
    filter_upwards [hle0, hle1, self_mem_nhdsWithin] with s h0 h1 hs
    rw [tjsl_trainJetSum_succ hCG hc0 htr hs j]
    exact add_le_add h0 h1

end UnforcedLeray.Short.PartI
