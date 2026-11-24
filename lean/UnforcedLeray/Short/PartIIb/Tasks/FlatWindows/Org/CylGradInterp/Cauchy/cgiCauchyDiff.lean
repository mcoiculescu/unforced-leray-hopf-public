import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T13_1_5_6_1
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.CylGradInterp.cgiLimitNorm

/-!
# `CgiCauchyDiff`: the derivatives `∂_i w n` are Cauchy in `L^r(cylMeas c)` (SP 1932-1933)

Apply the a priori inequality (`AprioriAt`, `λ = 1`) to `w n - w m`, use that `∂` is linear on
nice functions, and bound the right side by `H n + H m`, where `H n` is the error of the
approximant `w n`; `H n → 0` by `CgiApprox`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

open MeasureTheory Set Filter
open scoped ENNReal ContDiff Topology

theorem cgi1_le (c r : ℝ) (hr : 1 < r) : (1 : ℝ≥0∞) ≤ ENNReal.ofReal r := by
  rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hr.le

theorem cylNorm_sub_le_add' (c r : ℝ) (hr : 1 < r) {f g : Coord → ℂ}
    (hf : AEStronglyMeasurable f (cylMeas c)) (hg : AEStronglyMeasurable g (cylMeas c)) :
    cylNorm c r (fun x => f x - g x) ≤ cylNorm c r f + cylNorm c r g :=
  eLpNorm_sub_le hf hg (cgi1_le c r hr)

theorem cylNorm_sub_le_via (c r : ℝ) (hr : 1 < r) {f g h : Coord → ℂ}
    (hf : AEStronglyMeasurable f (cylMeas c)) (hg : AEStronglyMeasurable g (cylMeas c))
    (hh : AEStronglyMeasurable h (cylMeas c)) :
    cylNorm c r (fun x => f x - g x) ≤
      cylNorm c r (fun x => f x - h x) + cylNorm c r (fun x => h x - g x) := by
  have e : (fun x => f x - g x) = fun x => (f x - h x) + (h x - g x) := by
    funext x; ring
  rw [e]
  exact eLpNorm_add_le (hf.sub hh) (hh.sub hg) (cgi1_le c r hr)

theorem cylNorm_sub_comm (c r : ℝ) (f g : Coord → ℂ) :
    cylNorm c r (fun x => f x - g x) = cylNorm c r (fun x => g x - f x) :=
  eLpNorm_sub_comm _ _ _ _

theorem cdv_sub_fn (j : Fin 3) {f g : Coord → ℂ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    cdv j (fun x => f x - g x) = fun x => cdv j f x - cdv j g x := by
  funext x
  simp only [cdv, fderiv_fun_sub (hf.differentiable (by simp) x) (hg.differentiable (by simp) x),
    sub_apply]

theorem cdv2_sub_fn (k l : Fin 2) {f g : Coord → ℂ} (hf : ContDiff ℝ ∞ f)
    (hg : ContDiff ℝ ∞ g) :
    cdv k.succ (cdv l.succ (fun x => f x - g x)) =
      fun x => cdv k.succ (cdv l.succ f) x - cdv k.succ (cdv l.succ g) x := by
  rw [cdv_sub_fn l.succ hf hg]
  exact cdv_sub_fn k.succ (cdv_contDiff hf _) (cdv_contDiff hg _)

theorem cgiNice_sub (c r : ℝ) (hr : 1 < r) {f g : Coord → ℂ}
    (hf : CgiNice c r f) (hg : CgiNice c r g) : CgiNice c r (fun x => f x - g x) where
  smooth := hf.smooth.sub hg.smooth
  periodic := fun x => by simp only [hf.periodic x, hg.periodic x]
  mem0 := lt_of_le_of_lt
    (cylNorm_sub_le_add' c r hr hf.smooth.continuous.aestronglyMeasurable
      hg.smooth.continuous.aestronglyMeasurable)
    (ENNReal.add_lt_top.2 ⟨hf.mem0, hg.mem0⟩)
  mem1 := fun i => by
    rw [cdv_sub_fn i.succ hf.smooth hg.smooth]
    exact lt_of_le_of_lt
      (cylNorm_sub_le_add' c r hr (cdv_aesm c hf.smooth _) (cdv_aesm c hg.smooth _))
      (ENNReal.add_lt_top.2 ⟨hf.mem1 i, hg.mem1 i⟩)
  mem2 := fun k l => by
    rw [cdv2_sub_fn k l hf.smooth hg.smooth]
    exact lt_of_le_of_lt
      (cylNorm_sub_le_add' c r hr (cdv_aesm c (cdv_contDiff hf.smooth _) _)
        (cdv_aesm c (cdv_contDiff hg.smooth _) _))
      (ENNReal.add_lt_top.2 ⟨hf.mem2 k l, hg.mem2 k l⟩)

/-- The error `C (‖w - u‖ + Σ_{k,l} ‖∂_k∂_l w - D2 k l‖)` of an approximant `w`. -/
def cgiCauchyErr (c r C : ℝ) (u : Coord → ℂ) (D2 : Fin 2 → Fin 2 → Coord → ℂ)
    (w : Coord → ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal C * (cylNorm c r (fun x => w x - u x) +
    ∑ k : Fin 2, ∑ l : Fin 2, cylNorm c r (fun x => cdv k.succ (cdv l.succ w) x - D2 k l x))

theorem cgiCauchyDiff_proof : UnforcedLeray.Short.IIb.CgiCauchyDiff := by
  intro r hr c C hc hC hA u D2 w hw hum hD2 i ε hε
  obtain ⟨hnice, hu, hd2⟩ := hw
  have hacS : ∀ f : Coord → ℂ, AEStronglyMeasurable f volume →
      AEStronglyMeasurable f (cylMeas c) := fun f hf => hf.mono_ac (cylMeas_ac_volume c)
  have hum' := hacS u hum
  have hD2m : ∀ k l : Fin 2, AEStronglyMeasurable (D2 k l) (cylMeas c) :=
    fun k l => hacS _ (hD2 k l)
  have hwm : ∀ n, AEStronglyMeasurable (w n) (cylMeas c) :=
    fun n => (hnice n).smooth.continuous.aestronglyMeasurable
  have hbound : ∀ n m, cylNorm c r (fun x => cdv i.succ (w n) x - cdv i.succ (w m) x) ≤
      cgiCauchyErr c r C u D2 (w n) + cgiCauchyErr c r C u D2 (w m) := by
    intro n m
    have hgn := cgiNice_sub c r hr (hnice n) (hnice m)
    have hkey := hA _ hgn i 1 one_pos
    rw [cdv_sub_fn i.succ (hnice n).smooth (hnice m).smooth] at hkey
    simp only [inv_one, ENNReal.ofReal_one, one_mul] at hkey
    have hfirst : cylNorm c r (fun x => w n x - w m x) ≤
        cylNorm c r (fun x => w n x - u x) + cylNorm c r (fun x => w m x - u x) := by
      refine (cylNorm_sub_le_via c r hr (hwm n) (hwm m) hum').trans (le_of_eq ?_)
      rw [cylNorm_sub_comm c r u (w m)]
    have hterm : ∀ k l : Fin 2, cylNorm c r (cdv k.succ (cdv l.succ (fun x => w n x - w m x))) ≤
        cylNorm c r (fun x => cdv k.succ (cdv l.succ (w n)) x - D2 k l x) +
        cylNorm c r (fun x => cdv k.succ (cdv l.succ (w m)) x - D2 k l x) := by
      intro k l
      rw [cdv2_sub_fn k l (hnice n).smooth (hnice m).smooth]
      refine (cylNorm_sub_le_via c r hr (cdv_aesm c (cdv_contDiff (hnice n).smooth _) _)
        (cdv_aesm c (cdv_contDiff (hnice m).smooth _) _) (hD2m k l)).trans (le_of_eq ?_)
      rw [cylNorm_sub_comm c r (D2 k l) (cdv k.succ (cdv l.succ (w m)))]
    have hsum : ∑ k : Fin 2, ∑ l : Fin 2, cylNorm c r (cdv k.succ (cdv l.succ (fun x => w n x - w m x)))
        ≤ ∑ k : Fin 2, ∑ l : Fin 2, (cylNorm c r (fun x => cdv k.succ (cdv l.succ (w n)) x - D2 k l x) +
          cylNorm c r (fun x => cdv k.succ (cdv l.succ (w m)) x - D2 k l x)) :=
      Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun l _ => hterm k l
    calc cylNorm c r (fun x => cdv i.succ (w n) x - cdv i.succ (w m) x)
        ≤ ENNReal.ofReal C * (cylNorm c r (fun x => w n x - w m x) +
            ∑ k : Fin 2, ∑ l : Fin 2, cylNorm c r (cdv k.succ (cdv l.succ (fun x => w n x - w m x)))) :=
          hkey
      _ ≤ ENNReal.ofReal C * ((cylNorm c r (fun x => w n x - u x) +
            cylNorm c r (fun x => w m x - u x)) +
            ∑ k : Fin 2, ∑ l : Fin 2, (cylNorm c r (fun x => cdv k.succ (cdv l.succ (w n)) x - D2 k l x) +
              cylNorm c r (fun x => cdv k.succ (cdv l.succ (w m)) x - D2 k l x))) :=
          mul_le_mul_of_nonneg_left (add_le_add hfirst hsum) zero_le'
      _ = cgiCauchyErr c r C u D2 (w n) + cgiCauchyErr c r C u D2 (w m) := by
          unfold cgiCauchyErr
          simp only [Finset.sum_add_distrib]
          ring
  have hH : Tendsto (fun n => cgiCauchyErr c r C u D2 (w n)) atTop (𝓝 0) := by
    have e2 : Tendsto (fun n => ∑ k : Fin 2, ∑ l : Fin 2,
        cylNorm c r (fun x => cdv k.succ (cdv l.succ (w n)) x - D2 k l x)) atTop (𝓝 0) := by
      have := tendsto_finsetSum Finset.univ (fun k (_ : k ∈ Finset.univ) =>
        tendsto_finsetSum Finset.univ (fun l (_ : l ∈ Finset.univ) => hd2 k l))
      simpa using this
    have e3 := hu.add e2
    have e4 := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal C) e3 (Or.inr ENNReal.ofReal_ne_top)
    unfold cgiCauchyErr
    simpa using e4
  have hηpos : (0 : ℝ≥0∞) < min (ε / 2) 1 := lt_min (ENNReal.half_pos hε.ne') one_pos
  obtain ⟨N, hN⟩ := eventually_atTop.1 ((tendsto_order.1 hH).2 _ hηpos)
  refine ⟨N, fun m n hm hn => ?_⟩
  calc cylNorm c r (fun x => cdv i.succ (w n) x - cdv i.succ (w m) x)
      ≤ cgiCauchyErr c r C u D2 (w n) + cgiCauchyErr c r C u D2 (w m) := hbound n m
    _ < min (ε / 2) 1 + min (ε / 2) 1 := ENNReal.add_lt_add (hN n hn) (hN m hm)
    _ ≤ ε / 2 + ε / 2 := add_le_add (min_le_left _ _) (min_le_left _ _)
    _ = ε := ENNReal.add_halves ε

end UnforcedLeray.Short.IIb
