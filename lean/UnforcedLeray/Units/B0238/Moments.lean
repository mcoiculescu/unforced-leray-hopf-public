import UnforcedLeray.Units.B0238.Partials
import UnforcedLeray.Units.B0169
import UnforcedLeray.Lib.Gaussian.WeightedCell
import UnforcedLeray.Lib.Cylinder.Weight

/-!
# B0238 helpers: finite weighted moments of the Gaussian train data

Helper module of blueprint unit **B0238** (`unlabeled:4127`, `paper/main.tex` lines 4125–4134:
"its Gaussian data have the finite weighted moments used below"). The moments used below are
those of the full cell space `X_c = L²(C_c, (1+q²+η²)^m dq dη)` (tex 4171–4184) and of its
Sobolev versions `H^k_m` (tex 4149–4158): with the centred weight `Cyl.ρc z = 1 + q² + η²` on the
centred cell `[-c/2, c/2) × ℝ`, every derivative of the datum velocity `P_c v₀` and its vorticity
`P_c ω₀` have `∫_cell ρc^m ‖·‖^p < ∞` for every real `m` and every `p ≥ 1`, at every period
`c > 0` (no lower bound on `c` is needed for finiteness).

Device: on the centred cell `|q| ≤ c/2`, so `|q - nc| ≥ |n|c/2` and a Gaussian
`‖f(w)‖ ≤ A e^{-|w|²/8}` periodizes to `‖P_c f(q,η)‖ ≤ A S(c) e^{-η²/8}` with
`S(c) = ∑ₙ e^{-c²n²/32}` (`norm_periodize_le_on_cell`). The weight is at most
`(1+c²)^{|m|}(1+η²)^{|m|}` on the cell, which the Gaussian absorbs
(`integrableOn_cell_weight_of_gauss`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace UnforcedLeray.B0238

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec toVec)

/-- Lattice separation from the centred cell: `|q| ≤ c/2` gives `(nc)²/4 ≤ (q - nc)²`. -/
theorem sq_le_sq_sub_of_abs_le {c q : ℝ} (hc : 0 < c) (hq : |q| ≤ c / 2) (n : ℤ) :
    (n * c) ^ 2 / 4 ≤ (q - n * c) ^ 2 := by
  rcases abs_le.1 hq with ⟨hq1, hq2⟩
  rcases lt_trichotomy n 0 with hn | hn | hn
  · have hn' : (n : ℝ) + 1 ≤ 0 := by exact_mod_cast Int.lt_iff_add_one_le.1 hn
    have h1 : -(n * c) / 2 ≤ q - n * c := by nlinarith
    have h0 : 0 ≤ -(n * c) / 2 := by nlinarith
    nlinarith [mul_le_mul h1 h1 h0 (h0.trans h1)]
  · subst hn
    simp only [Int.cast_zero, zero_mul, sub_zero]
    norm_num
    positivity
  · have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have h1 : n * c / 2 ≤ n * c - q := by nlinarith
    have h0 : 0 ≤ n * c / 2 := by nlinarith
    nlinarith [mul_le_mul h1 h1 h0 (h0.trans h1)]

/-- `∑_{n∈ℤ} e^{-βn²}` converges for `β > 0`. -/
theorem summable_exp_neg_mul_int_sq {β : ℝ} (hβ : 0 < β) :
    Summable (fun n : ℤ => Real.exp (-β * (n : ℝ) ^ 2)) := by
  have hnat : Summable (fun n : ℕ => Real.exp (-β * ((n : ℤ) : ℝ) ^ 2)) := by
    refine (Gaussian.summable_exp_neg_mul_nat hβ).of_nonneg_of_le
      (fun n => (Real.exp_pos _).le) (fun n => ?_)
    rw [Real.exp_le_exp]
    push_cast
    have : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
      rcases Nat.eq_zero_or_pos n with h | h
      · simp [h]
      · have : (1 : ℝ) ≤ n := by exact_mod_cast h
        nlinarith
    nlinarith
  refine Summable.of_nat_of_neg hnat (hnat.congr fun n => ?_)
  push_cast
  ring_nf

/-- The lattice constant `S(c) = ∑_{n∈ℤ} e^{-c²n²/32}`. -/
def latticeConst (c : ℝ) : ℝ := ∑' n : ℤ, Real.exp (-(c ^ 2 / 32) * (n : ℝ) ^ 2)

theorem latticeConst_nonneg (c : ℝ) : 0 ≤ latticeConst c :=
  tsum_nonneg fun _ => (Real.exp_pos _).le

/-- **Gaussian bound of a periodization on the centred cell, for every period `c > 0`.**
If `‖f(w)‖ ≤ A e^{-|w|²/8}` then `‖P_c f(q,η)‖ ≤ A S(c) e^{-η²/8}` for `|q| ≤ c/2`. -/
theorem norm_periodize_le_on_cell {F : Type*} [NormedAddCommGroup F] {f : Plane → F} {A c : ℝ}
    (hc : 0 < c) (hf : ∀ w : Plane, ‖f w‖ ≤ A * Real.exp (-(w.1 ^ 2 + w.2 ^ 2) / 8))
    {z : Plane} (hz : z ∈ Cyl.cell c) :
    ‖Gaussian.periodize c f z‖ ≤ A * latticeConst c * Real.exp (-z.2 ^ 2 / 8) := by
  have hq : |z.1| ≤ c / 2 := abs_le.2 ⟨by linarith [hz.1.1], hz.1.2.le⟩
  have hβ : 0 < c ^ 2 / 32 := by positivity
  have hS := summable_exp_neg_mul_int_sq hβ
  have hA : 0 ≤ A := by
    have h0 := hf 0
    simp only [Prod.fst_zero, Prod.snd_zero] at h0
    norm_num at h0
    exact (norm_nonneg _).trans h0
  have hterm : ∀ n : ℤ, ‖f (z.1 - n * c, z.2)‖ ≤
      A * Real.exp (-z.2 ^ 2 / 8) * Real.exp (-(c ^ 2 / 32) * (n : ℝ) ^ 2) := by
    intro n
    refine (hf _).trans ?_
    rw [mul_assoc, ← Real.exp_add]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hA
    have h := sq_le_sq_sub_of_abs_le hc hq n
    simp only
    nlinarith
  have hsum : Summable (fun n : ℤ =>
      A * Real.exp (-z.2 ^ 2 / 8) * Real.exp (-(c ^ 2 / 32) * (n : ℝ) ^ 2)) := hS.mul_left _
  have hnorm : Summable (fun n : ℤ => ‖f (z.1 - n * c, z.2)‖) :=
    hsum.of_nonneg_of_le (fun _ => norm_nonneg _) hterm
  calc ‖Gaussian.periodize c f z‖ = ‖∑' n : ℤ, f (z.1 - n * c, z.2)‖ := rfl
    _ ≤ ∑' n : ℤ, ‖f (z.1 - n * c, z.2)‖ := norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' n : ℤ, A * Real.exp (-z.2 ^ 2 / 8) * Real.exp (-(c ^ 2 / 32) * (n : ℝ) ^ 2) :=
      hnorm.tsum_le_tsum hterm hsum
    _ = A * latticeConst c * Real.exp (-z.2 ^ 2 / 8) := by
      rw [tsum_mul_left, latticeConst]; ring

/-- The centred weight on the cell: `1 + q² + η² ≤ (1 + c²)(1 + η²)` for `|q| ≤ c/2`. -/
theorem ρc_le_on_cell {c : ℝ} {z : Plane} (hz : z ∈ Cyl.cell c) :
    Cyl.ρc z ≤ (1 + c ^ 2) * (1 + z.2 ^ 2) := by
  have h1 : z.1 ^ 2 ≤ c ^ 2 := by
    have hq1 := hz.1.1
    have hq2 := hz.1.2
    nlinarith
  rw [Cyl.ρc]
  nlinarith [sq_nonneg z.2, sq_nonneg c]

/-- **Finite weighted moments from a Gaussian bound on the cell.** If `h` is continuous and
`‖h(z)‖ ≤ B e^{-η²/8}` on the centred cell, then `∫_cell (1+q²+η²)^m ‖h‖^p < ∞` for every real
`m` and every `p ≥ 1` (stated as integrability, so no junk value of the integral enters). -/
theorem integrableOn_cell_weight_of_gauss {F : Type*} [NormedAddCommGroup F] {c : ℝ}
    {h : Plane → F} (hcont : Continuous h) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ z ∈ Cyl.cell c, ‖h z‖ ≤ B * Real.exp (-z.2 ^ 2 / 8)) (m : ℝ) {p : ℕ} (hp : 1 ≤ p) :
    IntegrableOn (fun z => Cyl.ρc z ^ m * ‖h z‖ ^ p) (Cyl.cell c) := by
  obtain ⟨K, hK0, hK⟩ := Gaussian.one_add_rpow_mul_exp_neg_quarter_le (abs_nonneg m)
  set C : ℝ := (1 + c ^ 2) ^ |m| * B ^ p * 4 ^ |m| * K with hC
  have hmeas : MeasurableSet (Cyl.cell c) := measurableSet_Ico.prod MeasurableSet.univ
  have hdom : Integrable (fun z : Plane => C * Real.exp (-(1 / 16) * z.2 ^ 2))
      ((volume : Measure Plane).restrict (Cyl.cell c)) := by
    rw [Cyl.volume_restrict_cell]
    exact Integrable.mul_prod (f := fun _ : ℝ => C) (g := fun η : ℝ => Real.exp (-(1 / 16) * η ^ 2))
      (integrableOn_const (by rw [Real.volume_Ico]; exact ENNReal.ofReal_ne_top))
      (integrable_exp_neg_mul_sq (by norm_num))
  refine hdom.mono' ((Cyl.continuous_rpow_ρc m).mul (hcont.norm.pow p)).aestronglyMeasurable ?_
  rw [ae_restrict_iff' hmeas]
  refine Eventually.of_forall fun z hz => ?_
  have hρ1 : 1 ≤ Cyl.ρc z := Cyl.one_le_ρc z
  have hm : Cyl.ρc z ^ m ≤ (1 + c ^ 2) ^ |m| * (4 ^ |m| * (1 + z.2 ^ 2 / 4) ^ |m|) := by
    calc Cyl.ρc z ^ m ≤ Cyl.ρc z ^ |m| := Real.rpow_le_rpow_of_exponent_le hρ1 (le_abs_self m)
      _ ≤ ((1 + c ^ 2) * (4 * (1 + z.2 ^ 2 / 4))) ^ |m| := by
        refine Real.rpow_le_rpow (by linarith) ?_ (abs_nonneg m)
        refine (ρc_le_on_cell hz).trans ?_
        exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = (1 + c ^ 2) ^ |m| * (4 ^ |m| * (1 + z.2 ^ 2 / 4) ^ |m|) := by
        rw [Real.mul_rpow (by positivity) (by positivity),
          Real.mul_rpow (by positivity) (by positivity)]
  have he1 : Real.exp (-z.2 ^ 2 / 8) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg z.2])
  have hh : ‖h z‖ ^ p ≤ B ^ p * Real.exp (-z.2 ^ 2 / 8) := by
    calc ‖h z‖ ^ p ≤ (B * Real.exp (-z.2 ^ 2 / 8)) ^ p :=
          pow_le_pow_left₀ (norm_nonneg _) (hb z hz) p
      _ = B ^ p * Real.exp (-z.2 ^ 2 / 8) ^ p := mul_pow _ _ _
      _ ≤ B ^ p * Real.exp (-z.2 ^ 2 / 8) := by
        gcongr
        exact pow_le_of_le_one (Real.exp_pos _).le he1 (by omega)
  have hsplit : Real.exp (-z.2 ^ 2 / 8) =
      Real.exp (-(z.2 ^ 2 / 4) / 4) * Real.exp (-(1 / 16) * z.2 ^ 2) := by
    rw [← Real.exp_add]; ring_nf
  have hK' := hK (z.2 ^ 2 / 4) (by positivity)
  rw [Real.norm_of_nonneg (by positivity)]
  calc Cyl.ρc z ^ m * ‖h z‖ ^ p
      ≤ ((1 + c ^ 2) ^ |m| * (4 ^ |m| * (1 + z.2 ^ 2 / 4) ^ |m|)) *
          (B ^ p * Real.exp (-z.2 ^ 2 / 8)) :=
        mul_le_mul hm hh (by positivity) (by positivity)
    _ = (1 + c ^ 2) ^ |m| * B ^ p * 4 ^ |m| *
          ((1 + z.2 ^ 2 / 4) ^ |m| * Real.exp (-(z.2 ^ 2 / 4) / 4)) *
          Real.exp (-(1 / 16) * z.2 ^ 2) := by
        rw [hsplit]; ring
    _ ≤ (1 + c ^ 2) ^ |m| * B ^ p * 4 ^ |m| * K * Real.exp (-(1 / 16) * z.2 ^ 2) := by
        gcongr
    _ = C * Real.exp (-(1 / 16) * z.2 ^ 2) := by rw [hC]

/-! ### The Gaussian train data -/

/-- **Weighted moments of every derivative of the datum velocity `P_c v₀`** (tex 4129–4131,
tex 2155–2156: "the Gaussian sums and all their derivatives … belong to every `H^j(C_c)`"):
for every `c > 0`, `j`, real `m` and `p ≥ 1`,
`∫_cell (1+q²+η²)^m ‖D^j(P_c v₀)‖^p < ∞`. -/
theorem integrableOn_weight_jet_trainDatum {c : ℝ} (hc : 0 < c) (j : ℕ) (m : ℝ) {p : ℕ}
    (hp : 1 ≤ p) :
    IntegrableOn (fun z => Cyl.ρc z ^ m * ‖iteratedFDeriv ℝ j (B0140.trainDatum c) z‖ ^ p)
      (Cyl.cell c) := by
  rw [B0169.trainDatum_eq_datum]
  obtain ⟨A, hA, hbA⟩ := Train.norm_iteratedFDeriv_v0_le j
  refine integrableOn_cell_weight_of_gauss
    ((Train.datum_contDiff hc.ne').continuous_iteratedFDeriv (by exact_mod_cast le_top))
    (mul_nonneg hA (latticeConst_nonneg c)) (fun z hz => ?_) m hp
  have e : iteratedFDeriv ℝ j (Train.datum c) z =
      Gaussian.periodize c (fun w => iteratedFDeriv ℝ j Train.v0 w) z :=
    congrFun (Train.jet_datum hc.ne' j) z
  rw [e]
  exact norm_periodize_le_on_cell hc hbA hz

/-- The datum `P_c v₀` is smooth (Gaussian sums with all derivatives, tex 2155). -/
theorem contDiff_trainDatum {c : ℝ} (hc : c ≠ 0) : ContDiff ℝ ∞ (B0140.trainDatum c) := by
  rw [B0169.trainDatum_eq_datum]; exact Train.datum_contDiff hc

/-- The datum vorticity `P_c ω₀` has a Gaussian bound on the centred cell, every `c > 0`. -/
theorem abs_curl_trainDatum_le {c : ℝ} (hc : 0 < c) {z : Plane} (hz : z ∈ Cyl.cell c) :
    |Cyl.curl (B0140.trainDatum c) z| ≤ 4 * latticeConst c * Real.exp (-z.2 ^ 2 / 8) := by
  rw [B0140.curl_trainDatum hc.ne', ← Real.norm_eq_abs]
  refine norm_periodize_le_on_cell hc (fun w => ?_) hz
  rw [B0169.vorticity_eq_omega0, Real.norm_eq_abs]
  refine (Train.omega0_abs_le w).trans (le_of_eq ?_)
  norm_num

/-- **Weighted moments of the datum vorticity `P_c ω₀`** (tex 4129–4131 and the space `X_c` of
tex 4171–4184): for every `c > 0`, real `m` and `p ≥ 1`, `∫_cell (1+q²+η²)^m |P_c ω₀|^p < ∞`. -/
theorem integrableOn_weight_curl_trainDatum {c : ℝ} (hc : 0 < c) (m : ℝ) {p : ℕ} (hp : 1 ≤ p) :
    IntegrableOn (fun z => Cyl.ρc z ^ m * |Cyl.curl (B0140.trainDatum c) z| ^ p) (Cyl.cell c) := by
  have h := integrableOn_cell_weight_of_gauss
    (continuous_curl ((contDiff_trainDatum hc.ne').of_le (by exact_mod_cast le_top)))
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) (latticeConst_nonneg c))
    (fun z hz => by rw [Real.norm_eq_abs]; exact abs_curl_trainDatum_le hc hz) m hp
  simpa only [Real.norm_eq_abs] using h

/-- The datum vorticity is integrable over the cell (`ω(0) ∈ L¹(C_c)`, tex 2156). -/
theorem integrableOn_curl_trainDatum {c : ℝ} (hc : 0 < c) :
    IntegrableOn (Cyl.curl (B0140.trainDatum c)) (Cyl.cell c) := by
  have h := integrableOn_weight_curl_trainDatum hc 0 (le_refl 1)
  simp only [Real.rpow_zero, one_mul, pow_one] at h
  have hm : AEStronglyMeasurable (Cyl.curl (B0140.trainDatum c))
      ((volume : Measure Plane).restrict (Cyl.cell c)) :=
    (continuous_curl ((contDiff_trainDatum hc.ne').of_le (by exact_mod_cast le_top))).aestronglyMeasurable
  refine (integrable_norm_iff hm).1 ?_
  simp only [Real.norm_eq_abs]
  exact h

end UnforcedLeray.B0238
