import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.Train.Defs
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.TrainJets.TrainVort
import UnforcedLeray.Short.PartI.Sub.PartI_T08_2_2.EnergyIneq
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDualitySub
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.ContDiff.Defs

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.IIIa

/-- The `q`-partial of a field is the `(1,0)`-derivative (`B0579.pd 0`). -/
theorem lad_pd0_eq {φ : ℝ × ℝ → ℝ} (hφ : Differentiable ℝ φ) (y : ℝ × ℝ) :
    UnforcedLeray.B0579.pd 0 φ y = deriv (fun t : ℝ => φ (t, y.2)) y.1 := by
  have h : HasDerivAt (fun t : ℝ => ((t, y.2) : ℝ × ℝ)) ((1, 0) : ℝ × ℝ) y.1 :=
    (hasDerivAt_id y.1).prodMk (hasDerivAt_const y.1 y.2)
  have h2 := (hφ y).hasFDerivAt.comp_hasDerivAt y.1 h
  have h3 : deriv (fun t : ℝ => φ (t, y.2)) y.1 = fderiv ℝ φ (y.1, y.2) (1, 0) := h2.deriv
  rw [h3]
  rfl

/-- The `η`-partial of a field is the `(0,1)`-derivative (`B0579.pd 1`). -/
theorem lad_pd1_eq {φ : ℝ × ℝ → ℝ} (hφ : Differentiable ℝ φ) (y : ℝ × ℝ) :
    UnforcedLeray.B0579.pd 1 φ y = deriv (fun t : ℝ => φ (y.1, t)) y.2 := by
  have h : HasDerivAt (fun t : ℝ => ((y.1, t) : ℝ × ℝ)) ((0, 1) : ℝ × ℝ) y.2 :=
    (hasDerivAt_const y.2 y.1).prodMk (hasDerivAt_id y.2)
  have h2 := (hφ y).hasFDerivAt.comp_hasDerivAt y.2 h
  have h3 : deriv (fun t : ℝ => φ (y.1, t)) y.2 = fderiv ℝ φ (y.1, y.2) (0, 1) := h2.deriv
  rw [h3]
  rfl

/-- A derivative of a function with period `c` is `c`-periodic. -/
theorem lad_deriv_periodic (f : ℝ → ℝ) (c : ℝ) (hf : ∀ t, f (t + c) = f t) (y : ℝ) :
    deriv f (y + c) = deriv f y := by
  have h1 : (fun x => f (x + c)) = f := funext hf
  have h2 := deriv_comp_add_const (f := f) (a := c) (x := y)
  rw [h1] at h2
  exact h2.symm

/-- The partials of a `c`-periodic-in-`q` field are `c`-periodic in `q` (integer shifts). -/
theorem lad_pd_int_periodic {φ : ℝ × ℝ → ℝ} (c : ℝ) (hφ : Differentiable ℝ φ)
    (hper : ∀ t s : ℝ, φ (t + c, s) = φ (t, s)) (j : Fin 2) (k : ℤ) (y : ℝ × ℝ) :
    UnforcedLeray.B0579.pd j φ (y.1 + k * c, y.2) = UnforcedLeray.B0579.pd j φ y := by
  fin_cases j
  · show UnforcedLeray.B0579.pd 0 φ (y.1 + k * c, y.2) = UnforcedLeray.B0579.pd 0 φ y
    rw [lad_pd0_eq hφ, lad_pd0_eq hφ]
    have hf : ∀ t : ℝ, (fun s : ℝ => φ (s, y.2)) (t + c) = (fun s : ℝ => φ (s, y.2)) t :=
      fun t => hper t y.2
    have hg : Function.Periodic (deriv (fun s : ℝ => φ (s, y.2))) c :=
      fun t => lad_deriv_periodic _ c hf t
    exact (hg.int_mul k) y.1
  · show UnforcedLeray.B0579.pd 1 φ (y.1 + k * c, y.2) = UnforcedLeray.B0579.pd 1 φ y
    rw [lad_pd1_eq hφ, lad_pd1_eq hφ]
    congr 1
    funext t
    have hg : Function.Periodic (fun s : ℝ => φ (s, t)) c := fun s => hper s t
    exact (hg.int_mul k) y.1

/-- The words `[1]` and `[2]` of the train vorticity are the partials of its slice. -/
theorem lad_tjW_pd {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c)
    (hE : ContDiffOn ℝ ∞ (tjE tr) tjU) {ρ : ℝ} (hρ : 0 ≤ ρ) (x : ℝ × ℝ) :
    tjW [1] (tjE tr) (ρ, x) = UnforcedLeray.B0579.pd 0 (UnforcedLeray.B0238.Ec tr ρ) x ∧
      tjW [2] (tjE tr) (ρ, x) = UnforcedLeray.B0579.pd 1 (UnforcedLeray.B0238.Ec tr ρ) x := by
  have hsl : ContDiff ℝ ∞ (fun z : ℝ × ℝ => tjE tr (ρ, z)) := by
    have : ContDiffOn ℝ ∞ (fun z : ℝ × ℝ => tjE tr (ρ, z)) univ :=
      hE.comp (contDiff_const.prodMk contDiff_id).contDiffOn
        (fun z _ => ⟨mem_Ici.2 hρ, mem_univ _⟩)
    exact contDiffOn_univ.1 this
  have hdiff : Differentiable ℝ (UnforcedLeray.B0238.Ec tr ρ) :=
    hsl.differentiable (by simp)
  constructor
  · rw [tjW_one_apply hE hρ x, lad_pd0_eq hdiff x]
  · rw [tjW_two_apply hE hρ x, lad_pd1_eq hdiff x]

/-- **The weighted gradient of the vorticity** (SP 270-288, 2866-2873): from `LadTrainBdd` on the
cell and the periodicity of the vorticity. -/
theorem tjLadGrad (m : ℝ) (hm : 8 < m) : TjLadGrad m := by
  intro ν c tr hc hLad a ha S hS
  obtain ⟨C, hC⟩ := hLad S hS
  refine ⟨C, fun ρ hρ x => ?_⟩
  have hρ0 : 0 ≤ ρ := hρ.1
  have hE : ContDiffOn ℝ ∞ (tjE tr) tjU := (tjTrainVort ν c tr).1
  have hper : ∀ t s : ℝ, UnforcedLeray.B0238.Ec tr ρ (t + c, s) = UnforcedLeray.B0238.Ec tr ρ (t, s) :=
    fun t s => by
      have := UnforcedLeray.Short.PartI.vjl_curl_periodic tr hρ0 (t, s)
      exact this
  have hdiff : Differentiable ℝ (UnforcedLeray.B0238.Ec tr ρ) := by
    have hsl : ContDiff ℝ ∞ (fun z : ℝ × ℝ => tjE tr (ρ, z)) := by
      have : ContDiffOn ℝ ∞ (fun z : ℝ × ℝ => tjE tr (ρ, z)) univ :=
        hE.comp (contDiff_const.prodMk contDiff_id).contDiffOn
          (fun z _ => ⟨mem_Ici.2 hρ0, mem_univ _⟩)
      exact contDiffOn_univ.1 this
    exact hsl.differentiable (by simp)
  have key : ∀ j : Fin 2, (1 + x.2 ^ 2) ^ ((m + 2) / 2) *
      |UnforcedLeray.B0579.pd j (UnforcedLeray.B0238.Ec tr ρ) x| ≤ C := by
    intro j
    have hq := toIcoMod_add_toIcoDiv_zsmul hc (-(c / 2)) x.1
    rw [zsmul_eq_mul] at hq
    have hmem : toIcoMod hc (-(c / 2)) x.1 ∈ Ico (-(c / 2)) (c / 2) := by
      have := toIcoMod_mem_Ico hc (-(c / 2)) x.1
      rw [show -(c / 2) + c = c / 2 by ring] at this
      exact this
    have hcell : (toIcoMod hc (-(c / 2)) x.1, x.2) ∈ UnforcedLeray.B0579.cell c :=
      ⟨hmem, mem_univ _⟩
    have h1 := (hC ρ ⟨hρ0, hρ.2⟩ _ hcell).2 j
    have hxe : x = (toIcoMod hc (-(c / 2)) x.1 + (toIcoDiv hc (-(c / 2)) x.1 : ℤ) * c, x.2) :=
      Prod.ext hq.symm rfl
    have hpd : UnforcedLeray.B0579.pd j (UnforcedLeray.B0238.Ec tr ρ) x =
        UnforcedLeray.B0579.pd j (UnforcedLeray.B0238.Ec tr ρ)
          (toIcoMod hc (-(c / 2)) x.1, x.2) := by
      conv_lhs => rw [hxe]
      exact lad_pd_int_periodic c hdiff hper j (toIcoDiv hc (-(c / 2)) x.1)
        (toIcoMod hc (-(c / 2)) x.1, x.2)
    have hjb : 1 + x.2 ^ 2 ≤ UnforcedLeray.B0579.jb (toIcoMod hc (-(c / 2)) x.1, x.2) := by
      unfold UnforcedLeray.B0579.jb
      dsimp only
      nlinarith [sq_nonneg (toIcoMod hc (-(c / 2)) x.1)]
    have hpow : (1 + x.2 ^ 2) ^ ((m + 2) / 2) ≤
        UnforcedLeray.B0579.jb (toIcoMod hc (-(c / 2)) x.1, x.2) ^ ((m + 2) / 2) :=
      Real.rpow_le_rpow (by positivity) hjb (by linarith)
    rw [hpd]
    calc (1 + x.2 ^ 2) ^ ((m + 2) / 2) *
          |UnforcedLeray.B0579.pd j (UnforcedLeray.B0238.Ec tr ρ) (toIcoMod hc (-(c / 2)) x.1, x.2)|
        ≤ UnforcedLeray.B0579.jb (toIcoMod hc (-(c / 2)) x.1, x.2) ^ ((m + 2) / 2) *
          |UnforcedLeray.B0579.pd j (UnforcedLeray.B0238.Ec tr ρ) (toIcoMod hc (-(c / 2)) x.1, x.2)| :=
          mul_le_mul_of_nonneg_right hpow (abs_nonneg _)
      _ ≤ C := h1
  fin_cases a
  · exact absurd rfl ha
  · show (1 + x.2 ^ 2) ^ ((m + 2) / 2) * |tjW [1] (tjE tr) (ρ, x)| ≤ C
    rw [(lad_tjW_pd tr hE hρ0 x).1]
    exact key 0
  · show (1 + x.2 ^ 2) ^ ((m + 2) / 2) * |tjW [2] (tjE tr) (ρ, x)| ≤ C
    rw [(lad_tjW_pd tr hE hρ0 x).2]
    exact key 1

end UnforcedLeray.Short.IIIa
