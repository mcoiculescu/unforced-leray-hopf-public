import UnforcedLeray.Units.B0140
import UnforcedLeray.Lib.Train.Datum

/-!
# B0141, datum part: the Gaussian sums on `C_c` (tex lines 2155–2157)

Blueprint unit **B0141** (`unlabeled:2152`, `paper/main.tex` lines 2152–2161), the facts about
the datum that the text checks itself: "The Gaussian sums and all their derivatives converge
uniformly, belong to every `H^j(C_c)`, and have vorticity in `L¹ ∩ L^∞` with zero integral"
(tex lines 2155–2157). Infrastructure: INF16 T1 (`Lib/Train/Datum.lean`), INF22 G7
(`Lib/Gaussian/Periodization.lean`, `Lib/Gaussian/PeriodizationCell.lean`), INF13 CY01
(`Lib/Cylinder/Basic.lean`).

**Conventions.** The datum is `Train.datum c = P_c v₀`, `P_c f(q,η) = ∑ₙ f(q - nc, η)`; it is
the datum `B0140.trainDatum c` of unit B0140 (`trainDatum_eq_datum`). Derivatives are Fréchet
jets `Train.jet j f = D^j f`. `H^j(C_c)` for a smooth field is "all jets of order `≤ j` lie in
`L²` of one unnormalized cell" (`MemHAll`, every order at once); the cell is `Cyl.cell c` with
Lebesgue measure `Cyl.cellμ c` (decision D1). Uniform convergence of a lattice sum on the
cylinder is uniform convergence of the finite partial sums (`Finset ℤ`, filter `atTop`) on
every band `|q| ≤ R`, in particular on the cell. All statements hold for every `c > 0`
(uniform convergence for `c ≠ 0`); the uniform-in-`c` bounds for `c ≥ 2` are
`Train.datum_bounds`.

Main declarations: `trainDatum_eq_datum`, `MemHAll`, `tendstoUniformlyOn_jet_datum`,
`tendstoUniformlyOn_jet_datum_cell`, `memHAll_datum`, `periodize_gauss_facts`, `stream0_facts`
(the stream sum `ψ(0) = P_c ψ₀`), `curl_datum_facts`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal

namespace UnforcedLeray.B0141

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Gaussian (periodize periodize_eq shiftVec)
open UnforcedLeray.Train (Vec toVec datum v0 jet)

/-! ### Identification with the datum of unit B0140 -/

/-- `v₀` in the `Vec` carrier is the INF16 profile `Train.v0` (copied from
`Units/B0169.lean`, `toVec_velocity`). -/
theorem toVec_velocity (w : Plane) : toVec (GaussianVortex.velocity w) = Train.v0 w := by
  have hg : Train.gauss0 w = GaussianVortex.planarGaussian w := by
    simp only [Train.gauss0, GaussianVortex.planarGaussian, GaussianVortex.radiusSq, neg_div]
  have e : GaussianVortex.velocity w =
      GaussianVortex.planarGaussian w • ((-w.2, w.1) : Plane) := by
    ext <;> simp [GaussianVortex.velocity, mul_comm]
  rw [Train.v0, hg, e, ← Train.toVecL_apply, map_smul, Train.toVecL_apply]

/-- The B0140 datum `v(q,η,0) = ∑ₙ v₀(q - nc, η)` (tex line 2146) is the INF16 T1 datum
`Train.datum` (copied from `Units/B0169.lean`, `trainDatum_eq_datum`). -/
theorem trainDatum_eq_datum (c : ℝ) : B0140.trainDatum c = datum c := by
  funext z
  rw [B0140.trainDatum_apply, Train.datum_apply, ← Train.toVecL_apply,
    Train.toVecL.map_tsum]
  simp only [Train.toVecL_apply, toVec_velocity]

/-! ### Lattice sums with a translate bound -/

section Periodize

variable {F : Type*} [NormedAddCommGroup F]

/-- A summable majorant of the translates on the band `|q| ≤ R`, from a translate bound
`‖g(q,η)‖ ≤ C (1+|q|)^{-2}` (Weierstrass M-test input). -/
theorem band_majorant {g : Plane → F} {C : ℝ}
    (hg : ∀ z : Plane, ‖g z‖ ≤ C * (1 + |z.1|) ^ (-(2 : ℝ))) {c : ℝ} (hc : c ≠ 0) (R : ℝ) :
    ∃ u : ℤ → ℝ, Summable u ∧
      ∀ (n : ℤ) (z : Plane), |z.1| ≤ R → ‖g (z.1 - n * c, z.2)‖ ≤ u n := by
  have hC : 0 ≤ C := by
    have h := hg 0
    simp only [Prod.fst_zero, abs_zero, add_zero, Real.one_rpow, mul_one] at h
    exact (norm_nonneg _).trans h
  refine ⟨fun n => C * ((1 + |R|) ^ (2 : ℝ) * (1 + |0 - n * c|) ^ (-(2 : ℝ))),
    ((Gaussian.summable_translate (s := 2) (by norm_num) hc 0).mul_left _).mul_left _, ?_⟩
  intro n z hz
  refine (hg _).trans (mul_le_mul_of_nonneg_left ?_ hC)
  have h := Gaussian.one_add_abs_rpow_neg_le (s := 2) (by norm_num) (z.1 - n * c) (-z.1)
  rw [show z.1 - n * c + -z.1 = 0 - n * c by ring, abs_neg] at h
  refine h.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
  exact Real.rpow_le_rpow (by positivity) (by linarith [le_abs_self R]) (by norm_num)

/-- **Uniform convergence of a lattice sum** (M-test): the partial sums of
`∑ₙ g(q - nc, η)` converge to `P_c g` uniformly on every band `|q| ≤ R`. -/
theorem tendstoUniformlyOn_periodize [CompleteSpace F] {g : Plane → F} {C : ℝ}
    (hg : ∀ z : Plane, ‖g z‖ ≤ C * (1 + |z.1|) ^ (-(2 : ℝ))) {c : ℝ} (hc : c ≠ 0) (R : ℝ) :
    TendstoUniformlyOn (fun t : Finset ℤ => fun z : Plane => ∑ n ∈ t, g (z.1 - n * c, z.2))
      (periodize c g) atTop {z : Plane | |z.1| ≤ R} := by
  obtain ⟨u, hu, hb⟩ := band_majorant hg hc R
  exact tendstoUniformlyOn_tsum hu (f := fun (n : ℤ) (z : Plane) => g (z.1 - n * c, z.2))
    fun n z hz => hb n z hz

/-- A lattice sum with a translate bound is bounded on the whole cylinder. -/
theorem norm_periodize_le_bound [CompleteSpace F] {g : Plane → F} {C : ℝ}
    (hg : ∀ z : Plane, ‖g z‖ ≤ C * (1 + |z.1|) ^ (-(2 : ℝ))) {c : ℝ} (hc : 0 < c) :
    ∃ M : ℝ, ∀ z : Plane, ‖periodize c g z‖ ≤ M := by
  obtain ⟨u, hu, hb⟩ := band_majorant hg hc.ne' c
  refine ⟨∑' n, u n, fun z => ?_⟩
  obtain ⟨y, hy, hyz⟩ := (Gaussian.periodic_periodize c g z.2).exists_mem_Ico₀ hc z.1
  have hz : periodize c g z = periodize c g (y, z.2) := hyz
  rw [hz]
  have hy' : |(y, z.2).1| ≤ c := abs_le.2 ⟨by linarith [hy.1], hy.2.le⟩
  exact tsum_of_norm_bounded hu.hasSum fun n => hb n (y, z.2) hy'

/-- **`L¹` on one cell** of the periodization of an integrable function (for every `c > 0`):
`∫_cell ‖P_c g‖ ≤ ∑ₙ ∫_cell ‖g(· - nc)‖ = ∫_{ℝ²} ‖g‖`. -/
theorem integrable_cell_periodize [NormedSpace ℝ F] {g : Plane → F} (hg : Integrable g) {c : ℝ}
    (hc : 0 < c) (hm : AEStronglyMeasurable (periodize c g) (Cyl.cellμ c)) :
    Integrable (periodize c g) (Cyl.cellμ c) := by
  refine ⟨hm, ?_⟩
  have hper : Cyl.IsPeriodic c (fun z => ‖periodize c g z‖ₑ) := fun z => by
    show ‖periodize c g (z.1 + c, z.2)‖ₑ = ‖periodize c g z‖ₑ
    rw [Gaussian.periodize_add_period]
  have hstrip := Cyl.lintegral_strip_eq_cell hc hper 0
  rw [zero_add] at hstrip
  have h1 : ∫⁻ z in Ico 0 c ×ˢ (univ : Set ℝ), ‖periodize c g z‖ₑ ≤
      ∫⁻ z in Gaussian.cell c, ∑' n : ℤ, ‖g (z - shiftVec c n)‖ₑ := by
    refine lintegral_mono fun z => ?_
    rw [periodize_eq]
    exact enorm_tsum_le_tsum_enorm
  have h2 : ∫⁻ z in Gaussian.cell c, ∑' n : ℤ, ‖g (z - shiftVec c n)‖ₑ = ∫⁻ w, ‖g w‖ₑ := by
    rw [lintegral_tsum fun n =>
      ((hg.comp_sub_right (shiftVec c n)).aestronglyMeasurable.enorm).restrict]
    exact Gaussian.tsum_setLIntegral_cell_translate (fun w => ‖g w‖ₑ) hc
  show ∫⁻ z, ‖periodize c g z‖ₑ ∂(Cyl.cellμ c) < ⊤
  rw [Cyl.cellμ, ← hstrip]
  exact (h1.trans_eq h2).trans_lt hg.2

end Periodize

/-- `L¹ ∩ L^∞ ⊆ L²`. -/
theorem memLp_two_of_integrable_of_bound {F : Type*} [NormedAddCommGroup F] {μ : Measure Plane}
    {f : Plane → F} (hf : Integrable f μ) {M : ℝ} (hM : ∀ z, ‖f z‖ ≤ M) : MemLp f 2 μ := by
  rw [memLp_two_iff_integrable_sq_norm hf.1]
  refine (hf.norm.const_mul M).mono' (hf.1.norm.pow 2) (Eventually.of_forall fun z => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc ‖f z‖ ^ 2 = ‖f z‖ * ‖f z‖ := sq _
    _ ≤ M * ‖f z‖ := mul_le_mul_of_nonneg_right (hM z) (norm_nonneg _)

/-! ### The datum: uniform convergence, `H^j`, vorticity -/

/-- Membership in every `H^j(C_c)` of a smooth field: all its derivatives lie in
`L²(cell)` (tex lines 2155–2156; scoping bypass B1, the `H^m` class of decision D8). For a
`C^∞` field the jets are the weak derivatives, so this is the Sobolev space. -/
def MemHAll (c : ℝ) (f : Plane → Vec) : Prop :=
  ∀ j : ℕ, MemLp (jet j f) 2 (Cyl.cellμ c)

/-- Every derivative of `v₀` is integrable on `ℝ²` (Gaussian bound, `Train.norm_iteratedFDeriv_v0_le`). -/
theorem integrable_jet_v0 (j : ℕ) : Integrable (jet j v0) := by
  obtain ⟨A, -, hb⟩ := Train.norm_iteratedFDeriv_v0_le j
  refine ((Gaussian.integrable_gauss_plane (a := 2) (by norm_num)).const_mul A).mono'
    ((Train.contDiff_v0 (n := ((⊤ : ℕ∞) : WithTop ℕ∞))).continuous_iteratedFDeriv
      (by exact_mod_cast le_top)).aestronglyMeasurable (Eventually.of_forall fun w => ?_)
  have e : (4 : ℝ) * 2 = 8 := by norm_num
  rw [e]
  exact hb w

/-- **The Gaussian sums and all their derivatives converge uniformly** (tex lines 2155–2156):
for `c ≠ 0`, every order `j` and every band `|q| ≤ R`, the partial sums of
`∑ₙ D^j v₀(q - nc, η)` converge uniformly to `D^j(P_c v₀)`. -/
theorem tendstoUniformlyOn_jet_datum {c : ℝ} (hc : c ≠ 0) (j : ℕ) (R : ℝ) :
    TendstoUniformlyOn
      (fun t : Finset ℤ => fun z : Plane => ∑ n ∈ t, jet j v0 (z.1 - n * c, z.2))
      (jet j (datum c)) atTop {z : Plane | |z.1| ≤ R} := by
  obtain ⟨C, hC⟩ := Train.v0_translate_bound j
  rw [Train.jet_datum hc j]
  exact tendstoUniformlyOn_periodize (g := jet j v0) hC hc R

/-- The same on the cell `C_c ≅ [-c/2, c/2) × ℝ`. -/
theorem tendstoUniformlyOn_jet_datum_cell {c : ℝ} (hc : 0 < c) (j : ℕ) :
    TendstoUniformlyOn
      (fun t : Finset ℤ => fun z : Plane => ∑ n ∈ t, jet j v0 (z.1 - n * c, z.2))
      (jet j (datum c)) atTop (Cyl.cell c) :=
  (tendstoUniformlyOn_jet_datum hc.ne' j (c / 2)).mono fun z hz =>
    abs_le.2 ⟨by have := hz.1.1; linarith, hz.1.2.le⟩

/-- **The datum lies in every `H^j(C_c)`** (tex line 2156), for every `c > 0`. -/
theorem memHAll_datum {c : ℝ} (hc : 0 < c) : MemHAll c (datum c) := by
  intro j
  obtain ⟨C, hC⟩ := Train.v0_translate_bound j
  have hcont : Continuous (jet j (datum c)) :=
    (Train.datum_contDiff hc.ne').continuous_iteratedFDeriv (by exact_mod_cast le_top)
  rw [Train.jet_datum hc.ne' j] at hcont ⊢
  have hI := integrable_cell_periodize (integrable_jet_v0 j) hc hcont.aestronglyMeasurable
  obtain ⟨M, hM⟩ := norm_periodize_le_bound (g := jet j v0) hC hc
  exact memLp_two_of_integrable_of_bound hI hM

/-! ### Generic Gaussian profiles (used for the stream `ψ(0) = P_c ψ₀`) -/

section GaussProfile

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace F] in
/-- A Gaussian bound `A e^{-(q²+η²)/8}` gives a translate bound `C (1+|q|)^{-2}`. -/
theorem gauss_translate_bound {g : Plane → F} {k : ℕ} {A : ℝ} (hA : 0 ≤ A)
    (hb : ∀ w : Plane, ‖iteratedFDeriv ℝ k g w‖ ≤ A * Real.exp (-(w.1 ^ 2 + w.2 ^ 2) / 8)) :
    ∃ C : ℝ, ∀ z : Plane, ‖iteratedFDeriv ℝ k g z‖ ≤ C * (1 + |z.1|) ^ (-(2 : ℝ)) := by
  obtain ⟨K, -, hk⟩ := Train.exp_neg_sq_div_eight_le_rpow
  refine ⟨A * K, fun z => (hb z).trans ?_⟩
  have h1 : Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8) ≤ Real.exp (-z.1 ^ 2 / 8) :=
    Real.exp_le_exp.2 (by nlinarith [sq_nonneg z.2])
  calc A * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8) ≤ A * (K * (1 + |z.1|) ^ (-(2 : ℝ))) :=
        mul_le_mul_of_nonneg_left (h1.trans (hk z.1)) hA
    _ = A * K * (1 + |z.1|) ^ (-(2 : ℝ)) := by ring

/-- **Lattice sums of a smooth Gaussian profile** (every derivative `≤ A_k e^{-|w|²/8}`), for
`c > 0` and every order `j`: termwise differentiation `D^j(P_c g) = P_c(D^j g)`, uniform
convergence of the partial sums of `∑ₙ D^j g(q - nc, η)` on the cell, and `D^j(P_c g)` in
`L²(cell)`. -/
theorem periodize_gauss_facts {g : Plane → F} (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g)
    (hb : ∀ k : ℕ, ∃ A : ℝ, 0 ≤ A ∧
      ∀ w : Plane, ‖iteratedFDeriv ℝ k g w‖ ≤ A * Real.exp (-(w.1 ^ 2 + w.2 ^ 2) / 8))
    {c : ℝ} (hc : 0 < c) (j : ℕ) :
    jet j (periodize c g) = periodize c (jet j g) ∧
    TendstoUniformlyOn
      (fun t : Finset ℤ => fun z : Plane => ∑ n ∈ t, jet j g (z.1 - n * c, z.2))
      (jet j (periodize c g)) atTop (Cyl.cell c) ∧
    MemLp (jet j (periodize c g)) 2 (Cyl.cellμ c) := by
  have hD : ∀ k : ℕ, (k : ℕ∞) ≤ (⊤ : ℕ∞) → ∃ C : ℝ, ∀ z : Plane,
      ‖iteratedFDeriv ℝ k g z‖ ≤ C * (1 + |z.1|) ^ (-(2 : ℝ)) := fun k _ => by
    obtain ⟨A, hA, hbk⟩ := hb k
    exact gauss_translate_bound hA hbk
  have hj : jet j (periodize c g) = periodize c (jet j g) := by
    funext z
    have h := Gaussian.iteratedFDeriv_periodize (N := ⊤) (s := 2) (by norm_num) hc.ne' hg hD
      (m := j) le_top
    simp only [jet]
    rw [h, periodize_eq]
    rfl
  have hcont : Continuous (jet j (periodize c g)) :=
    (Gaussian.contDiff_periodize (N := ⊤) (s := 2) (by norm_num) hc.ne' hg
      hD).continuous_iteratedFDeriv (by exact_mod_cast le_top)
  obtain ⟨C, hC⟩ := hD j le_top
  have hint : Integrable (jet j g) := by
    obtain ⟨A, -, hbj⟩ := hb j
    refine ((Gaussian.integrable_gauss_plane (a := 2) (by norm_num)).const_mul A).mono'
      (hg.continuous_iteratedFDeriv (by exact_mod_cast le_top)).aestronglyMeasurable
      (Eventually.of_forall fun w => ?_)
    have e : (4 : ℝ) * 2 = 8 := by norm_num
    rw [e]
    exact hbj w
  refine ⟨hj, ?_, ?_⟩
  · rw [hj]
    exact (tendstoUniformlyOn_periodize (g := jet j g) hC hc.ne' (c / 2)).mono fun z hz =>
      abs_le.2 ⟨by have := hz.1.1; linarith, hz.1.2.le⟩
  · rw [hj] at hcont ⊢
    have hI := integrable_cell_periodize hint hc hcont.aestronglyMeasurable
    obtain ⟨M, hM⟩ := norm_periodize_le_bound (g := jet j g) hC hc
    exact memLp_two_of_integrable_of_bound hI hM

end GaussProfile

/-- **The stream sum `ψ(0) = P_c ψ₀ = -2∑ₙ e^{-|z-(nc,0)|²/4}`** (tex line 2050; the Gaussian
sum of the stream, tex lines 2155–2156), for `c > 0` and every order `j`: its partial sums and
those of all its derivatives converge uniformly on the cell, and `D^j ψ(0) ∈ L²(cell)`. -/
theorem stream0_facts {c : ℝ} (hc : 0 < c) (j : ℕ) :
    TendstoUniformlyOn
      (fun t : Finset ℤ => fun z : Plane => ∑ n ∈ t, jet j Train.psi0 (z.1 - n * c, z.2))
      (jet j (Train.stream0 c)) atTop (Cyl.cell c) ∧
    MemLp (jet j (Train.stream0 c)) 2 (Cyl.cellμ c) :=
  let h := periodize_gauss_facts (g := Train.psi0) Train.contDiff_psi0
    Train.norm_iteratedFDeriv_psi0_le hc j
  ⟨h.2.1, h.2.2⟩

/-- The translate bound of `ω₀`: `|ω₀(q,η)| ≤ C (1+|q|)^{-2}`. -/
theorem omega0_translate_bound :
    ∃ C : ℝ, ∀ z : Plane, ‖Train.omega0 z‖ ≤ C * (1 + |z.1|) ^ (-(2 : ℝ)) := by
  obtain ⟨K, -, hk⟩ := Train.exp_neg_sq_div_eight_le_rpow
  refine ⟨4 * K, fun z => ?_⟩
  rw [Real.norm_eq_abs]
  refine (Train.omega0_abs_le z).trans ?_
  have h1 : Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / (4 * 2)) ≤ Real.exp (-z.1 ^ 2 / 8) :=
    Real.exp_le_exp.2 (by nlinarith [sq_nonneg z.2])
  calc 4 * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / (4 * 2))
      ≤ 4 * (K * (1 + |z.1|) ^ (-(2 : ℝ))) := by
        have := h1.trans (hk z.1); linarith
    _ = 4 * K * (1 + |z.1|) ^ (-(2 : ℝ)) := by ring

/-- **The datum vorticity lies in `L¹ ∩ L^∞` of `C_c` with zero integral** (tex lines
2156–2157), for every `c > 0`: `ω(·,0) = curl(P_c v₀) = P_c ω₀` is integrable on one cell,
bounded on the whole cylinder, and `∫_cell ω(·,0) = 0`. -/
theorem curl_datum_facts {c : ℝ} (hc : 0 < c) :
    Integrable (Cyl.curl (datum c)) (Cyl.cellμ c) ∧
      (∃ M : ℝ, ∀ z : Plane, |Cyl.curl (datum c) z| ≤ M) ∧
      ∫ z in Cyl.cell c, Cyl.curl (datum c) z = 0 := by
  have hcurl : Cyl.curl (datum c) = periodize c Train.omega0 :=
    funext fun z => Train.datum_curl hc.ne' z
  have hom : Train.omega0 = GaussianVortex.vorticity := by
    funext w
    simp only [Train.omega0, Train.gauss0, GaussianVortex.vorticity,
      GaussianVortex.planarGaussian, GaussianVortex.radiusSq, neg_div]
  have hint : Integrable Train.omega0 := by rw [hom]; exact GaussianVortex.integrable_vorticity
  obtain ⟨C, hC⟩ := omega0_translate_bound
  have homc : Continuous Train.omega0 := by
    unfold Train.omega0 Train.gauss0; fun_prop
  have hcont : Continuous (periodize c Train.omega0) := by
    have h := Gaussian.continuous_tsum_translates homc (s := 2) (by norm_num) hc.ne' hC
    have e : periodize c Train.omega0 = fun y => ∑' n : ℤ, Train.omega0 (y - shiftVec c n) :=
      funext fun y => periodize_eq c Train.omega0 y
    rw [e]; exact h
  obtain ⟨M, hM⟩ := norm_periodize_le_bound hC hc
  refine ⟨?_, ⟨M, fun z => ?_⟩, Train.integral_cell_curl_datum hc⟩
  · rw [hcurl]
    exact integrable_cell_periodize hint hc hcont.aestronglyMeasurable
  · rw [hcurl, ← Real.norm_eq_abs]; exact hM z

end UnforcedLeray.B0141
