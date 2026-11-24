import UnforcedLeray.Short.PartIIa.Sub.R08_2
import UnforcedLeray.Lib.AxisymmetricB.FlatExtension

/-!
# Part II-a, task `PartII-a:R08/2` leaf: `AxisFlatSmooth` (smoothness at nonzero axis points)

Source of record: `the November 2 reference manuscript`, lines 1330-1334 ("Each
derivative costs `C/r`; all powers of `|x|/r` are absorbed by the Gaussian decay in `η = Rz/r`";
"including smoothness at nonzero axis points").

Target `AxisFlatSmooth` (`Sub/R08_2.lean`): a field `f`, `C^∞` off the axis, `0` on the axis and
flat on every `flatRegion δ M` (`δ > 0`) with some `κ > 0`, is `C^∞` at every axis point `x₀`
with `x₀ 2 ≠ 0`.

Proof. Let `a = |x₀ 2| > 0`, and take `κ` from the hypothesis for `δ = a/2`, `M = 2a`. Let `ψ`
be the smooth bump on `Space` centred at `x₀` with `rIn = a/4` and `rOut = a/2`. Its iterated
derivatives are bounded (compact support). The product `g = ψ • f` vanishes on the axis, is
`C^∞` off the axis, and is flat with the same `κ`: at points within `a/2` of `x₀` the Leibniz rule
applies on `flatRegion`, and at points farther away `g` vanishes on a neighbourhood. The flat
extension lemma `Axi.contDiff_flat_extension` then gives `C^k` for every finite `k`, since the
extension by zero of `g` is `g` itself. Finally `f = g` on the ball `B(x₀, a/4)`.

Helpers are prefixed `afs`. The Leibniz lemma `afs_leibniz` repeats `fsm_leibniz` of
`Tasks/R08InletSolenoidal/InletSmoothExt/FlatSmul.lean`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIa

/-- Powers of `r ∈ (0, 1]` are ordered: `1 / r^k ≤ 1 / r^N` for `k ≤ N`. -/
theorem afs_inv_pow_le {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) {k N : ℕ} (h : k ≤ N) :
    1 / r ^ k ≤ 1 / r ^ N :=
  one_div_le_one_div_of_le (pow_pos hr N) (pow_le_pow_of_le_one hr.le hr1 h)

/-- Replacing the constant by its absolute value only enlarges the bound. -/
theorem afs_abs_le (C r e : ℝ) (k : ℕ) (hr : 0 ≤ r) (he : 0 ≤ e) :
    C / r ^ k * e ≤ |C| / r ^ k * e := by
  refine mul_le_mul_of_nonneg_right ?_ he
  exact div_le_div_of_nonneg_right (le_abs_self C) (pow_nonneg hr k)

/-- Pointwise Leibniz bound for `z ↦ f z • g z` on the open set `axisᶜ`. -/
theorem afs_leibniz {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Space → ℝ} {g : Space → E} {y : Space}
    (hfS : ContDiffOn ℝ ∞ f Axi.axisᶜ) (hgS : ContDiffOn ℝ ∞ g Axi.axisᶜ) (hy : y ∈ Axi.axisᶜ)
    (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun z => f z • g z) y‖ ≤
      ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i f y‖ *
        ‖iteratedFDeriv ℝ (n - i) g y‖ := by
  have hB : ‖(ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] E →L[ℝ] E)‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_lsmul_le
  have h1 : ‖iteratedFDerivWithin ℝ n (fun z => f z • g z) Axi.axisᶜ y‖ ≤
      ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ‖iteratedFDerivWithin ℝ i f Axi.axisᶜ y‖ *
        ‖iteratedFDerivWithin ℝ (n - i) g Axi.axisᶜ y‖ :=
    ContinuousLinearMap.norm_iteratedFDerivWithin_le_of_bilinear_of_le_one
      (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] E →L[ℝ] E) hfS hgS
      Axi.isOpen_compl_axis.uniqueDiffOn hy (by exact_mod_cast le_top) hB
  have eF : ∀ m : ℕ, iteratedFDerivWithin ℝ m f Axi.axisᶜ y = iteratedFDeriv ℝ m f y :=
    fun m => iteratedFDerivWithin_of_isOpen m Axi.isOpen_compl_axis hy
  have eG : ∀ m : ℕ, iteratedFDerivWithin ℝ m g Axi.axisᶜ y = iteratedFDeriv ℝ m g y :=
    fun m => iteratedFDerivWithin_of_isOpen m Axi.isOpen_compl_axis hy
  have eP : iteratedFDerivWithin ℝ n (fun z => f z • g z) Axi.axisᶜ y =
      iteratedFDeriv ℝ n (fun z => f z • g z) y :=
    iteratedFDerivWithin_of_isOpen n Axi.isOpen_compl_axis hy
  rw [eP] at h1
  simp only [eF, eG] at h1
  exact h1

/-- Arithmetic of one Leibniz term: `c P Q ≤ c |B| |C| (1/r^N · e)` when `P ≤ |B|` and
`Q ≤ |C|/r^k · e` with `k ≤ N`, `0 < r ≤ 1`. -/
theorem afs_term (c P B Q C r e : ℝ) (k N : ℕ) (hc : 0 ≤ c) (hPB : P ≤ |B|) (hQ : 0 ≤ Q)
    (hQC : Q ≤ |C| / r ^ k * e) (hr : 0 < r) (hr1 : r ≤ 1) (he : 0 ≤ e) (hkN : k ≤ N) :
    c * P * Q ≤ c * |B| * |C| * (1 / r ^ N * e) := by
  have hpow : 1 / r ^ k ≤ 1 / r ^ N := afs_inv_pow_le hr hr1 hkN
  have h1 : c * P ≤ c * |B| := mul_le_mul_of_nonneg_left hPB hc
  have h2 : c * P * Q ≤ c * |B| * (|C| / r ^ k * e) :=
    mul_le_mul h1 hQC hQ (mul_nonneg hc (abs_nonneg _))
  have h3 : |C| / r ^ k * e ≤ |C| * (1 / r ^ N * e) := by
    have e1 : |C| / r ^ k * e = |C| * (1 / r ^ k) * e := by ring
    rw [e1]
    have e2 : |C| * (1 / r ^ k) * e ≤ |C| * (1 / r ^ N) * e :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (abs_nonneg _)) he
    have e3 : |C| * (1 / r ^ N) * e = |C| * (1 / r ^ N * e) := by ring
    linarith
  calc c * P * Q ≤ c * |B| * (|C| / r ^ k * e) := h2
    _ ≤ c * |B| * (|C| * (1 / r ^ N * e)) :=
        mul_le_mul_of_nonneg_left h3 (mul_nonneg hc (abs_nonneg _))
    _ = c * |B| * |C| * (1 / r ^ N * e) := by ring

/-- A bump function on `Space` has bounded iterated derivatives (compact support). -/
theorem afs_cutoff_bdd {x₀ : Space} (ψ : ContDiffBump x₀) (n : ℕ) :
    ∃ B : ℝ, ∀ y : Space, ‖iteratedFDeriv ℝ n (⇑ψ) y‖ ≤ B := by
  have hC : ContDiff ℝ ∞ (⇑ψ) := ψ.contDiff
  have hc : Continuous (iteratedFDeriv ℝ n (⇑ψ)) :=
    hC.continuous_iteratedFDeriv (by exact_mod_cast le_top)
  have hcs : HasCompactSupport (iteratedFDeriv ℝ n (⇑ψ)) :=
    ψ.hasCompactSupport.iteratedFDeriv n
  obtain ⟨B, hB⟩ := hc.bounded_above_of_compact_support hcs
  exact ⟨B, hB⟩

/-- The coordinate `y ↦ y 2` is `1`-Lipschitz for the Euclidean distance. -/
theorem afs_abs_coord_le (x y : Space) : |y 2 - x 2| ≤ dist y x := by
  have hc : (y - x) 2 = y 2 - x 2 := by simp
  have hsq : |y 2 - x 2| ^ 2 ≤ ‖y - x‖ ^ 2 := by
    rw [sq_abs, Axi.norm_sq_eq_ϱ_sq_add (y - x), hc]
    nlinarith [sq_nonneg (Axi.ϱ (y - x))]
  rw [dist_eq_norm]
  exact (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).1 hsq

/-- **`PartII-a:R08/2` leaf `AxisFlatSmooth`**: a field which is `C^∞` off the axis, vanishes on
the axis and is flat near the axis away from `z = 0`, is `C^∞` at every axis point with `z ≠ 0`. -/
theorem axisFlatSmooth : AxisFlatSmooth := by
  unfold AxisFlatSmooth
  intro f hf hf0 hflat x₀ _hx₀ hx₀2
  obtain ⟨a, ha⟩ : ∃ a : ℝ, |x₀ 2| = a := ⟨_, rfl⟩
  have ha0 : 0 < a := by rw [← ha]; exact abs_pos.2 hx₀2
  obtain ⟨κ, hκ, hFO⟩ := hflat (a / 2) (2 * a) (by linarith)
  unfold FlatOn at hFO
  obtain ⟨-, hfb⟩ := hFO
  choose Cf Nf hCf using hfb
  obtain ⟨ψ, hψin, hψout⟩ : ∃ ψ : ContDiffBump x₀, ψ.rIn = a / 4 ∧ ψ.rOut = a / 2 :=
    ⟨⟨a / 4, a / 2, by linarith, by linarith⟩, rfl, rfl⟩
  have hψS : ContDiff ℝ ∞ (⇑ψ) := ψ.contDiff
  have hψbd : ∀ n : ℕ, ∃ B : ℝ, ∀ y : Space, ‖iteratedFDeriv ℝ n (⇑ψ) y‖ ≤ B :=
    fun n => afs_cutoff_bdd ψ n
  choose Bψ hBψ using hψbd
  have hgS : ContDiffOn ℝ ∞ (fun y => ψ y • f y) Axi.axisᶜ :=
    hψS.contDiffOn.smul hf
  -- the flatness bound for the product `g = ψ • f`, with the same `κ`
  have hkey : ∀ n : ℕ, ∃ (C : ℝ) (N : ℕ), ∀ y : Space, y ∉ Axi.axis → Axi.ϱ y < 1 →
      ‖iteratedFDeriv ℝ n (fun z => ψ z • f z) y‖ ≤
        C / Axi.ϱ y ^ N * Real.exp (-κ / Axi.ϱ y ^ 2) := by
    intro n
    have hC0 : 0 ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * |Bψ i| * |Cf (n - i)| :=
      Finset.sum_nonneg (fun i _ => by positivity)
    refine ⟨∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * |Bψ i| * |Cf (n - i)|,
      ∑ j ∈ Finset.range (n + 1), Nf (n - j), ?_⟩
    intro y hy hy1
    have hr : 0 < Axi.ϱ y := Axi.ϱ_pos hy
    by_cases hd : dist y x₀ ≤ a / 2
    · -- Leibniz branch: `y` lies in `flatRegion (a/2) (2a)`.
      have hd' : |y 2 - x₀ 2| ≤ a / 2 := (afs_abs_coord_le x₀ y).trans hd
      have hA := abs_sub_abs_le_abs_sub (x₀ 2) (y 2)
      have hB := abs_sub_abs_le_abs_sub (y 2) (x₀ 2)
      have hC := abs_sub_comm (x₀ 2) (y 2)
      have hlow : a / 2 ≤ |y 2| := by linarith
      have hup : |y 2| ≤ 2 * a := by linarith
      have hyW : y ∈ flatRegion (a / 2) (2 * a) := by
        show y ∉ Axi.axis ∧ Axi.ϱ y < 1 ∧ a / 2 ≤ |y 2| ∧ |y 2| ≤ 2 * a
        exact ⟨hy, hy1, hlow, hup⟩
      have hyS : y ∈ Axi.axisᶜ := hy
      have hL := afs_leibniz (f := ⇑ψ) (g := f) hψS.contDiffOn hf hyS n
      calc ‖iteratedFDeriv ℝ n (fun z => ψ z • f z) y‖
          ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (⇑ψ) y‖ *
              ‖iteratedFDeriv ℝ (n - i) f y‖ := hL
        _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * |Bψ i| * |Cf (n - i)| *
              (1 / Axi.ϱ y ^ (∑ j ∈ Finset.range (n + 1), Nf (n - j)) *
                Real.exp (-κ / Axi.ϱ y ^ 2)) := by
          apply Finset.sum_le_sum
          intro i hi
          have hkN : Nf (n - i) ≤ ∑ j ∈ Finset.range (n + 1), Nf (n - j) :=
            Finset.single_le_sum (f := fun j => Nf (n - j)) (fun j _ => Nat.zero_le _) hi
          exact afs_term (n.choose i : ℝ) _ (Bψ i) _ (Cf (n - i)) (Axi.ϱ y)
            (Real.exp (-κ / Axi.ϱ y ^ 2)) (Nf (n - i)) (∑ j ∈ Finset.range (n + 1), Nf (n - j))
            (by positivity) ((hBψ i y).trans (le_abs_self _)) (norm_nonneg _)
            ((hCf (n - i) y hyW).trans
              (afs_abs_le (Cf (n - i)) (Axi.ϱ y) (Real.exp (-κ / Axi.ϱ y ^ 2)) (Nf (n - i))
                hr.le (Real.exp_pos _).le))
            hr (hy1.le) (Real.exp_pos _).le hkN
        _ = (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * |Bψ i| * |Cf (n - i)|) *
              (1 / Axi.ϱ y ^ (∑ j ∈ Finset.range (n + 1), Nf (n - j)) *
                Real.exp (-κ / Axi.ϱ y ^ 2)) := by
          rw [Finset.sum_mul]
        _ = (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * |Bψ i| * |Cf (n - i)|) /
              Axi.ϱ y ^ (∑ j ∈ Finset.range (n + 1), Nf (n - j)) *
                Real.exp (-κ / Axi.ϱ y ^ 2) := by
          ring
    · -- Zero branch: `g` vanishes on a neighbourhood of `y`.
      have hd' : a / 2 < dist y x₀ := not_le.1 hd
      have hcont : Continuous (fun z : Space => dist z x₀) :=
        continuous_id.dist continuous_const
      have hU : {z : Space | a / 2 < dist z x₀} ∈ 𝓝 y :=
        (isOpen_lt continuous_const hcont).mem_nhds hd'
      have hgz : (fun z => ψ z • f z) =ᶠ[𝓝 y] (fun _ : Space => (0 : Space)) := by
        filter_upwards [hU] with z hz
        have hz' : a / 2 < dist z x₀ := hz
        have hz0 : ψ z = 0 := ψ.zero_of_le_dist (x := z) (by rw [hψout]; exact hz'.le)
        simp [hz0]
      have hnorm0 : ‖iteratedFDeriv ℝ n (fun z => ψ z • f z) y‖ = 0 := by
        rw [(hgz.iteratedFDeriv ℝ n).eq_of_nhds]
        simp [iteratedFDeriv_fun_zero]
      rw [hnorm0]
      exact mul_nonneg (div_nonneg hC0 (pow_nonneg (Axi.ϱ_nonneg y) _)) (Real.exp_nonneg _)
  choose Cg Ng hCg using hkey
  have hgk : ∀ k : ℕ, ContDiffOn ℝ k (fun y => ψ y • f y) Axi.axisᶜ :=
    fun k => hgS.of_le (by exact_mod_cast le_top)
  -- the extension by zero of `g` is `g` itself
  have hext : Axi.extendByZeroOnAxis (fun y => ψ y • f y) = fun y => ψ y • f y := by
    funext y
    by_cases hy : y ∈ Axi.axis
    · simp only [Axi.extendByZeroOnAxis_of_mem hy, hf0 y hy, smul_zero]
    · exact Axi.extendByZeroOnAxis_of_not_mem hy
  have hgC : ∀ k : ℕ, ContDiff ℝ k (fun y => ψ y • f y) := by
    intro k
    have h := Axi.contDiff_flat_extension (k := k) (hgk k) hκ Cg Ng
      (fun n _ y hy hy1 => hCg n y hy hy1)
    rwa [hext] at h
  -- `f = g` on a neighbourhood of `x₀`
  have hfg : f =ᶠ[𝓝 x₀] (fun y => ψ y • f y) := by
    filter_upwards [Metric.ball_mem_nhds x₀ (show (0 : ℝ) < a / 4 by linarith)] with y hy
    have hψ1 : ψ y = 1 := by
      apply ψ.one_of_mem_closedBall
      rw [hψin]
      exact Metric.ball_subset_closedBall hy
    simp [hψ1]
  rw [contDiffAt_infty]
  intro k
  exact ((hgC k).contDiffAt).congr_of_eventuallyEq hfg

end UnforcedLeray.Short.PartIIa
