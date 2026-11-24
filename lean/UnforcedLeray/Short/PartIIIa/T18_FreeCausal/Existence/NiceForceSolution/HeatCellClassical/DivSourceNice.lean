import UnforcedLeray.Short.PartIIIa.Sub.T18_2_4_1

/-!
# Part III-a, task `PartIII-a:T18/2/4/1/5`: the divergence source is nice

Target: `DivSourceNice` (`Sub/T18_2_4_1.lean`). For a `NiceForce` `F`, `i : Fin 2` and `μ : ℂ`,
the scalar `s^μ Σ_j ∂_j F_ij` is a `NiceScalar`. Source of record:
`the November 2 reference manuscript`, the nice-force clause of the
proof (the statement lives in `Sub/T18_2_4_1.lean` with the citation SP 3427-3440).

Proof outline. Write `D_i p = Σ_j fderiv (F · i j) p (0, dir j)` (joint derivative in the
direction `(0, dir j)`, which equals the slice derivative `pdC j`). Then:
smoothness of `D_i` from `ContDiff.fderiv_right`; `c`-periodicity from `fderiv_comp_add_right`;
vanishing of `D_i` on the three open pieces by `Filter.EventuallyEq.fderiv_eq`; and smoothness of
`s ↦ s^μ` on `s > 0` from `Complex.cpow_def_of_ne_zero`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-! ## Helpers -/

/-- The slice derivative in `y` is the joint derivative in the direction `(0, v)`. -/
theorem divSN_slice_fderiv (g : ℝ × (ℝ × ℝ) → ℂ) (hg : ContDiff ℝ ∞ g) (s : ℝ) (x v : ℝ × ℝ) :
    fderiv ℝ (fun y => g (s, y)) x v = fderiv ℝ g (s, x) (0, v) := by
  have h1 : HasFDerivAt (fun y : ℝ × ℝ => ((s, y) : ℝ × (ℝ × ℝ)))
      (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ)) x :=
    hasFDerivAt_prodMk_right s x
  have hgd : DifferentiableAt ℝ g (s, x) := hg.differentiable (by simp) _
  have hfd : fderiv ℝ (fun y => g (s, y)) x
      = (fderiv ℝ g (s, x)).comp (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ)) :=
    (hgd.hasFDerivAt.comp x h1).fderiv
  rw [hfd, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply]

/-- The joint derivative form of `D_i`: `D_i p = Σ_j fderiv (F · i j) p (0, dir j)`. -/
def divSN_D (F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ) (i : Fin 2) (p : ℝ × (ℝ × ℝ)) : ℂ :=
  ∑ j : Fin 2, fderiv ℝ (fun q => F q i j) p (0, B0579.dir j)

theorem divSN_pdC_eq (F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ)
    (hF : ∀ i j, ContDiff ℝ ∞ fun p => F p i j) (i j : Fin 2) (p : ℝ × (ℝ × ℝ)) :
    pdC j (fun y => F (p.1, y) i j) p.2 = fderiv ℝ (fun q => F q i j) p (0, B0579.dir j) := by
  unfold pdC
  exact divSN_slice_fderiv (fun q => F q i j) (hF i j) p.1 p.2 (B0579.dir j)

theorem divSN_fderiv_zero {G : ℝ × (ℝ × ℝ) → ℂ} {q : ℝ × (ℝ × ℝ)} (v : ℝ × (ℝ × ℝ))
    (h : G =ᶠ[𝓝 q] fun _ => (0 : ℂ)) : fderiv ℝ G q v = 0 := by
  rw [h.fderiv_eq, fderiv_const_apply, zero_apply]

theorem divSN_fderiv_per (G : ℝ × (ℝ × ℝ) → ℂ) (c : ℝ)
    (hG : ∀ (s : ℝ) (x : ℝ × ℝ), G (s, (x.1 + c, x.2)) = G (s, x)) (s : ℝ) (x : ℝ × ℝ) :
    fderiv ℝ G (s, (x.1 + c, x.2)) = fderiv ℝ G (s, x) := by
  have hτ : ((s, (x.1 + c, x.2)) : ℝ × (ℝ × ℝ)) = (s, x) + (0, (c, 0)) := by
    ext <;> simp
  have hfun : (fun w : ℝ × (ℝ × ℝ) => G (w + (0, (c, 0)))) = G := by
    funext w
    have hw : w + (0, (c, 0)) = (w.1, (w.2.1 + c, w.2.2)) := by
      ext <;> simp
    rw [hw]
    exact hG w.1 w.2
  have key : fderiv ℝ (fun w : ℝ × (ℝ × ℝ) => G (w + (0, (c, 0)))) (s, x)
      = fderiv ℝ G ((s, x) + (0, (c, 0))) := fderiv_comp_add_right _
  rw [hfun, ← hτ] at key
  exact key.symm

theorem divSN_D_per (F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ) (c : ℝ)
    (hper : ∀ (s : ℝ) (x : ℝ × ℝ) (i j : Fin 2), F (s, (x.1 + c, x.2)) i j = F (s, x) i j)
    (i : Fin 2) (s : ℝ) (x : ℝ × ℝ) :
    divSN_D F i (s, (x.1 + c, x.2)) = divSN_D F i (s, x) := by
  unfold divSN_D
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [divSN_fderiv_per (fun q => F q i j) c (fun s' x' => hper s' x' i j) s x]

theorem divSN_D_contDiff (F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ)
    (hF : ∀ i j, ContDiff ℝ ∞ fun p => F p i j) (i : Fin 2) :
    ContDiff ℝ ∞ (divSN_D F i) := by
  unfold divSN_D
  refine ContDiff.sum (fun j _ => ?_)
  exact ((hF i j).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem divSN_D_zero (F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ) (aF BF RF : ℝ)
    (hz : ∀ (s : ℝ) (x : ℝ × ℝ) (i j : Fin 2), (s < aF ∨ BF < s ∨ RF < |x.2|) → F (s, x) i j = 0)
    (i : Fin 2) (q : ℝ × (ℝ × ℝ)) (hq : q.1 < aF ∨ BF < q.1 ∨ RF < |q.2.2|) :
    divSN_D F i q = 0 := by
  unfold divSN_D
  refine Finset.sum_eq_zero (fun j _ => ?_)
  apply divSN_fderiv_zero
  rcases hq with h | h | h
  · have hopen : IsOpen {r : ℝ × (ℝ × ℝ) | r.1 < aF} :=
      isOpen_lt continuous_fst continuous_const
    have hqmem : q ∈ {r : ℝ × (ℝ × ℝ) | r.1 < aF} := h
    filter_upwards [hopen.mem_nhds hqmem] with r hr
    exact hz r.1 r.2 i j (Or.inl hr)
  · have hopen : IsOpen {r : ℝ × (ℝ × ℝ) | BF < r.1} :=
      isOpen_lt continuous_const continuous_fst
    have hqmem : q ∈ {r : ℝ × (ℝ × ℝ) | BF < r.1} := h
    filter_upwards [hopen.mem_nhds hqmem] with r hr
    exact hz r.1 r.2 i j (Or.inr (Or.inl hr))
  · have hopen : IsOpen {r : ℝ × (ℝ × ℝ) | RF < |r.2.2|} :=
      isOpen_lt continuous_const (continuous_snd.comp continuous_snd).abs
    have hqmem : q ∈ {r : ℝ × (ℝ × ℝ) | RF < |r.2.2|} := h
    filter_upwards [hopen.mem_nhds hqmem] with r hr
    exact hz r.1 r.2 i j (Or.inr (Or.inr hr))

/-- `s ↦ (s : ℂ)^μ` is smooth on `s > 0`. -/
theorem divSN_cpow_contDiffAt (μ : ℂ) (s0 : ℝ) (hs0 : 0 < s0) :
    ContDiffAt ℝ ∞ (fun s : ℝ => (s : ℂ) ^ μ) s0 := by
  have hlog : ContDiffAt ℝ ∞ (fun s : ℝ => Real.log s) s0 := Real.contDiffAt_log.2 hs0.ne'
  have hof : ContDiffAt ℝ ∞ (fun t : ℝ => (t : ℂ)) (Real.log s0) :=
    Complex.ofRealCLM.contDiff.contDiffAt
  have hcl : ContDiffAt ℝ ∞ (fun s : ℝ => ((Real.log s : ℝ) : ℂ)) s0 := hof.comp s0 hlog
  have hexp : ContDiffAt ℝ ∞ (fun s : ℝ => Complex.exp (((Real.log s : ℝ) : ℂ) * μ)) s0 :=
    (Complex.contDiff_exp : ContDiff ℝ ∞ Complex.exp).contDiffAt.comp s0
      (hcl.mul (contDiffAt_const (c := μ)))
  refine hexp.congr_of_eventuallyEq ?_
  filter_upwards [lt_mem_nhds hs0] with s hs
  show (s : ℂ) ^ μ = Complex.exp (((Real.log s : ℝ) : ℂ) * μ)
  have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  rw [Complex.cpow_def_of_ne_zero hs', ← Complex.ofReal_log hs.le]

/-! ## The nice scalar -/

theorem divSN_nice (c : ℝ) (μ : ℂ) (F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ) (hN : NiceForce c F)
    (i : Fin 2) :
    NiceScalar c (fun p : ℝ × (ℝ × ℝ) => (p.1 : ℂ) ^ μ * divSN_D F i p) := by
  unfold NiceForce at hN
  obtain ⟨-, hsm, hper, aF, BF, RF, haF, hz⟩ := hN
  unfold NiceScalar
  refine ⟨?_, ?_, aF, BF, RF, haF, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro p
    by_cases hp : 0 < p.1
    · exact ((divSN_cpow_contDiffAt μ p.1 hp).comp p contDiff_fst.contDiffAt).mul
        (divSN_D_contDiff F hsm i).contDiffAt
    · have hpa : p.1 < aF := lt_of_le_of_lt (not_lt.mp hp) haF
      have hopen : IsOpen {r : ℝ × (ℝ × ℝ) | r.1 < aF} :=
        isOpen_lt continuous_fst continuous_const
      have hpmem : p ∈ {r : ℝ × (ℝ × ℝ) | r.1 < aF} := hpa
      refine (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : ℝ × (ℝ × ℝ) => (0 : ℂ)) p).congr_of_eventuallyEq ?_
      filter_upwards [hopen.mem_nhds hpmem] with r hr
      show (r.1 : ℂ) ^ μ * divSN_D F i r = 0
      rw [divSN_D_zero F aF BF RF hz i r (Or.inl hr), mul_zero]
  · intro s x
    dsimp only
    rw [divSN_D_per F c hper i s x]
  · intro s x hx
    dsimp only
    rw [divSN_D_zero F aF BF RF hz i (s, x) hx, mul_zero]

/-! ## Main theorem -/

theorem divSourceNice : UnforcedLeray.Short.IIIa.DivSourceNice := by
  unfold DivSourceNice
  intro c μ F hN i
  have hF : ∀ i j, ContDiff ℝ ∞ fun p => F p i j := by
    unfold NiceForce at hN
    exact hN.2.1
  have e : (fun p : ℝ × (ℝ × ℝ) => (p.1 : ℂ) ^ μ * ∑ j : Fin 2, pdC j (fun y => F (p.1, y) i j) p.2)
      = (fun p : ℝ × (ℝ × ℝ) => (p.1 : ℂ) ^ μ * divSN_D F i p) := by
    funext p
    congr 1
    unfold divSN_D
    exact Finset.sum_congr rfl (fun j _ => divSN_pdC_eq F hF i j p)
  rw [e]
  exact divSN_nice c μ F hN i

end UnforcedLeray.Short.IIIa

end
