import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.HkStep.Energy.Static.Algebra

/-!
# `PartIII-a:T21/2/7/2/1/1/5/18/2`: regularity of the pieces of the mollified rate

Source of record: `the November 2 reference manuscript` lines 3060-3071 (the
energies `E_j` are classical quantities of the regularized adjoint).  From the shared mollifier
leaves (`CellMollSmooth`, `CellConvDeriv`, `CellMollWeakDeriv`, `HkStep/Shared.lean`):

* the base field of a jet is periodic and in `X_{-m,c}`;
* `adjSpatial w (ρ_n ⋆ f) = ρ_n ⋆ D w` for a jet `D` of `f` (`st_adjSpatial_cellMoll_jet`, as
  `adjSpatial_cellMoll_jet` of `HkStep/Assembly.lean`);
* `v_l φ` is periodic and in `X_{-m,c}` (`st_velMul_memLp`);
* the transport term is `stTrans v n φ = Σ_l ∂_l (ρ_n ⋆ (v_l φ))` (`st_trans_eq`), smooth, periodic,
  with all partials in `X_{-m,c}` (`st_trans_reg`);
* `∂^w ΔG = Δ ∂^w G` for smooth `G` (`st_adjSpatial_stLap`, from `StAdjComm`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

theorem st_molKer_contDiff (n : ℕ) : ContDiff ℝ ∞ (molKer n) :=
  (molBump n).contDiff_normed

theorem st_molKer_hasCompactSupport (n : ℕ) : HasCompactSupport (molKer n) :=
  (molBump n).hasCompactSupport_normed

theorem st_jet_periodic {c m : ℝ} {k : ℕ} {f : ℝ × ℝ → ℂ} {D : List (Fin 2) → ℝ × ℝ → ℂ}
    (h : IsCellJet c m k f D) : ∀ x : ℝ × ℝ, f (x.1 + c, x.2) = f x := by
  have := h.periodic [] (Nat.zero_le _)
  rwa [h.base] at this

theorem st_jet_memX {c m : ℝ} {k : ℕ} {f : ℝ × ℝ → ℂ} {D : List (Fin 2) → ℝ × ℝ → ℂ}
    (h : IsCellJet c m k f D) : MemLp f 2 (B0579.cellMeasure c (-m)) := by
  have := h.memX [] (Nat.zero_le _)
  rwa [h.base] at this

/-- The classical partials of the mollification of a jet are the mollified fields. -/
theorem st_adjSpatial_cellMoll_jet (hW : CellMollWeakDeriv) {c m : ℝ} (hc : 0 < c) {k : ℕ}
    {f : ℝ × ℝ → ℂ} {D : List (Fin 2) → ℝ × ℝ → ℂ} (hJ : IsCellJet c m k f D) (n : ℕ) :
    ∀ w : List (Fin 2), w.length ≤ k → adjSpatial w (cellMoll n f) = cellMoll n (D w)
  | [], _ => by rw [hJ.base]; rfl
  | j :: w, hw => by
    have hw' : w.length < k := by simpa using hw
    show pdCx j (adjSpatial w (cellMoll n f)) = cellMoll n (D (j :: w))
    rw [st_adjSpatial_cellMoll_jet hW hc hJ n w hw'.le]
    exact hW c m j (D w) (D (j :: w)) hc (hJ.periodic w hw'.le) (hJ.periodic (j :: w) hw)
      (hJ.memX w hw'.le) (hJ.memX (j :: w) hw) (hJ.deriv j w hw') n

/-! ## The slice velocity -/

theorem st_vel_contDiff {c : ℝ} {v : ℝ × ℝ → EuclideanSpace ℝ (Fin 2)} {Av : ℕ → ℝ}
    (hv : SliceVel c v Av) (l : Fin 2) : ContDiff ℝ ∞ (stVel v l) := by
  have h : stVel v l = fun x => (EuclideanSpace.proj l : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ) (v x) :=
    rfl
  rw [h]
  exact (EuclideanSpace.proj l : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff.comp hv.1

theorem st_vel_abs_le {c : ℝ} {v : ℝ × ℝ → EuclideanSpace ℝ (Fin 2)} {Av : ℕ → ℝ}
    (hv : SliceVel c v Av) (l : Fin 2) (x : ℝ × ℝ) : |stVel v l x| ≤ Av 0 := by
  have h1 : ‖v x l‖ ≤ ‖v x‖ := PiLp.norm_apply_le (v x) l
  have h2 : ‖iteratedFDeriv ℝ 0 v x‖ ≤ Av 0 := hv.2.2.2 0 x
  rw [norm_iteratedFDeriv_zero] at h2
  rw [Real.norm_eq_abs] at h1
  exact h1.trans h2

theorem st_vel_periodic {c : ℝ} {v : ℝ × ℝ → EuclideanSpace ℝ (Fin 2)} {Av : ℕ → ℝ}
    (hv : SliceVel c v Av) (l : Fin 2) (x : ℝ × ℝ) : stVel v l (x.1 + c, x.2) = stVel v l x := by
  show v (x.1 + c, x.2) l = v x l
  rw [hv.2.1 x]

theorem st_Av0_nonneg {c : ℝ} {v : ℝ × ℝ → EuclideanSpace ℝ (Fin 2)} {Av : ℕ → ℝ}
    (hv : SliceVel c v Av) : 0 ≤ Av 0 :=
  (abs_nonneg _).trans (st_vel_abs_le hv 0 0)

theorem st_velMul_periodic {c : ℝ} {v : ℝ × ℝ → EuclideanSpace ℝ (Fin 2)} {Av : ℕ → ℝ}
    (hv : SliceVel c v Av) {φ : ℝ × ℝ → ℂ} (hφ : ∀ x : ℝ × ℝ, φ (x.1 + c, x.2) = φ x)
    (l : Fin 2) (x : ℝ × ℝ) :
    (fun y => ((v y l : ℝ) : ℂ) * φ y) (x.1 + c, x.2) = (fun y => ((v y l : ℝ) : ℂ) * φ y) x := by
  simp only
  rw [hv.2.1 x, hφ x]

theorem st_velMul_memLp {c m : ℝ} {v : ℝ × ℝ → EuclideanSpace ℝ (Fin 2)} {Av : ℕ → ℝ}
    (hv : SliceVel c v Av) {φ : ℝ × ℝ → ℂ} (hφ : MemLp φ 2 (B0579.cellMeasure c (-m)))
    (l : Fin 2) : MemLp (fun y => ((v y l : ℝ) : ℂ) * φ y) 2 (B0579.cellMeasure c (-m)) := by
  have hcont : Continuous fun y => ((v y l : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (st_vel_contDiff hv l).continuous
  refine hφ.of_le_mul (c := Av 0) (hcont.aestronglyMeasurable.mul hφ.1)
    (ae_of_all _ fun y => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (st_vel_abs_le hv l y) (norm_nonneg _)

/-! ## The transport term -/

theorem st_trans_eq (hCD : CellConvDeriv) {c m : ℝ} (hc : 0 < c)
    {v : ℝ × ℝ → EuclideanSpace ℝ (Fin 2)} {Av : ℕ → ℝ} (hv : SliceVel c v Av)
    {φ : ℝ × ℝ → ℂ} (hφp : ∀ x : ℝ × ℝ, φ (x.1 + c, x.2) = φ x)
    (hφm : MemLp φ 2 (B0579.cellMeasure c (-m))) (n : ℕ) :
    stTrans v n φ = fun x =>
      ∑ l : Fin 2, pdCx l (cellMoll n (fun y => ((v y l : ℝ) : ℂ) * φ y)) x := by
  funext x
  unfold stTrans
  refine Finset.sum_congr rfl fun l _ => ?_
  have h := (hCD c m (molKer n) (fun y => ((v y l : ℝ) : ℂ) * φ y) hc (st_molKer_contDiff n)
    (st_molKer_hasCompactSupport n) (st_velMul_periodic hv hφp l)
    (st_velMul_memLp hv hφm l)).2.2 [l]
  exact (congrFun h x).symm

theorem st_trans_reg (hS : CellMollSmooth) (hCD : CellConvDeriv) {c m : ℝ} (hc : 0 < c)
    {v : ℝ × ℝ → EuclideanSpace ℝ (Fin 2)} {Av : ℕ → ℝ} (hv : SliceVel c v Av)
    {φ : ℝ × ℝ → ℂ} (hφp : ∀ x : ℝ × ℝ, φ (x.1 + c, x.2) = φ x)
    (hφm : MemLp φ 2 (B0579.cellMeasure c (-m))) (n : ℕ) :
    ContDiff ℝ ∞ (stTrans v n φ) ∧
      (∀ x : ℝ × ℝ, stTrans v n φ (x.1 + c, x.2) = stTrans v n φ x) ∧
      ∀ w : List (Fin 2), MemLp (adjSpatial w (stTrans v n φ)) 2 (B0579.cellMeasure c (-m)) := by
  rw [st_trans_eq hCD hc hv hφp hφm n]
  have hP := fun l : Fin 2 =>
    hS c m n (fun y => ((v y l : ℝ) : ℂ) * φ y) hc (st_velMul_periodic hv hφp l)
      (st_velMul_memLp hv hφm l)
  have hPs : ∀ l : Fin 2,
      ContDiff ℝ ∞ (pdCx l (cellMoll n (fun y => ((v y l : ℝ) : ℂ) * φ y))) :=
    fun l => st_contDiff_pdCx (hP l).1 l
  refine ⟨?_, ?_, ?_⟩
  · simp only [Fin.sum_univ_two]
    exact (hPs 0).add (hPs 1)
  · intro x
    simp only [Fin.sum_univ_two]
    rw [st_pdCx_periodic (hP 0).2.1 0 x, st_pdCx_periodic (hP 1).2.1 1 x]
  · intro w
    rw [st_adjSpatial_sum2 hPs w]
    simp only [Fin.sum_univ_two]
    have hm : ∀ l : Fin 2, MemLp (adjSpatial w (pdCx l (cellMoll n
        (fun y => ((v y l : ℝ) : ℂ) * φ y)))) 2 (B0579.cellMeasure c (-m)) := by
      intro l
      have := (hP l).2.2 (w ++ [l])
      rwa [st_adjSpatial_append] at this
    exact (hm 0).add (hm 1)

/-! ## The Laplacian -/

theorem st_contDiff_stLap {G : ℝ × ℝ → ℂ} (hG : ContDiff ℝ ∞ G) : ContDiff ℝ ∞ (stLap G) :=
  (st_contDiff_adjSpatial hG [0, 0]).add (st_contDiff_adjSpatial hG [1, 1])

theorem st_adjSpatial_stLap (hComm : StAdjComm) {G : ℝ × ℝ → ℂ} (hG : ContDiff ℝ ∞ G)
    (w : List (Fin 2)) :
    adjSpatial w (stLap G) = fun x =>
      pdCx 0 (pdCx 0 (adjSpatial w G)) x + pdCx 1 (pdCx 1 (adjSpatial w G)) x := by
  have e : ∀ l : Fin 2, adjSpatial w (adjSpatial [l, l] G) = pdCx l (pdCx l (adjSpatial w G)) := by
    intro l
    show adjSpatial w (pdCx l (pdCx l G)) = _
    rw [hComm (pdCx l G) (st_contDiff_pdCx hG l) w l, hComm G hG w l]
  unfold stLap
  rw [st_adjSpatial_add (st_contDiff_adjSpatial hG [0, 0]) (st_contDiff_adjSpatial hG [1, 1]) w,
    e 0, e 1]

end UnforcedLeray.Short.IIIa
