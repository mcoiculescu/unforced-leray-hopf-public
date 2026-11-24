import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.Dense.Defs

/-!
# Smoothness of the Ward fields (`PartIII-b:IIIb-D2/3/2/11/3`)

Source 4171-4173, 4276-4282: pointwise calculus.  For jointly `C^∞` fields `U`, `X` and a
jointly `C^∞` scalar `p`, the fields `[U, X]`, `D_{μ+1}X`, `Ẽ_μ` and `X·∇p` are jointly `C^∞`.
The key tool is `ContDiff.fderiv`: the spatial derivative of a jointly smooth family is jointly
smooth (`fs_fderiv`); time derivatives are obtained from the same lemma after the change of
variables `(τ, y) ↦ (y, τ)` (`fs_deriv_time`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem fs_top_add : ((⊤ : ℕ∞) : WithTop ℕ∞) + 1 ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
  first
    | simp
    | exact le_of_eq (by norm_cast)
    | exact le_rfl

/-- The spatial derivative of a jointly smooth family is jointly smooth. -/
theorem fs_fderiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : ℝ → Space → E}
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ × Space => F x.1 x.2)) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ × Space => fderiv ℝ (F x.1) x.2) := by
  have hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (Function.uncurry (fun (x : ℝ × Space) (y : Space) => F x.1 y)) :=
    hF.comp ((contDiff_fst.comp contDiff_fst).prodMk contDiff_snd)
  exact ContDiff.fderiv hf contDiff_snd fs_top_add

/-- The time derivative of a jointly smooth family is jointly smooth. -/
theorem fs_deriv_time {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : ℝ → Space → E}
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ × Space => F x.1 x.2)) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ × Space => deriv (fun t => F t x.2) x.1) := by
  have hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (Function.uncurry (fun (x : ℝ × Space) (t : ℝ) => F t x.2)) :=
    hF.comp (contDiff_snd.prodMk (contDiff_snd.comp contDiff_fst))
  have h2 := ContDiff.fderiv hf (contDiff_fst : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
    (fun x : ℝ × Space => x.1)) fs_top_add
  have h3 := h2.clm_apply
    (contDiff_const : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun _ : ℝ × Space => (1 : ℝ)))
  exact h3

/-- A coordinate of a jointly smooth vector field. -/
theorem fs_coord {g : ℝ × Space → Space} (j : Fin 3)
    (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => g x j) :=
  (contDiff_piLp_apply (p := (2 : ENNReal)) (i := j)).comp hg

theorem fs_pd {F : ℝ → Space → Space}
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ × Space => F x.1 x.2)) (j : Fin 3) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ × Space => physPd (F x.1) j x.2) :=
  (fs_fderiv hF).clm_apply contDiff_const

theorem fs_pd2 {F : ℝ → Space → Space}
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ × Space => F x.1 x.2)) (j l : Fin 3) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ × Space => physPd2 (F x.1) j l x.2) := by
  have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : ℝ × Space => physPd (F x.1) l x.2) := fs_pd hF l
  exact fs_pd (F := fun τ y => physPd (F τ) l y) h1 j

theorem fs_lap {F : ℝ → Space → Space}
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ × Space => F x.1 x.2)) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ × Space => physLap (F x.1) x.2) := by
  have h := ContDiff.sum (s := Finset.univ)
    (f := fun (j : Fin 3) (x : ℝ × Space) => physPd2 (F x.1) j j x.2)
    (fun j _ => fs_pd2 hF j j)
  exact h

theorem fs_dmu {X : ℝ → Space → Space}
    (hX : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ × Space => X x.1 x.2))
    (ν μ : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ × Space => physDmu ν μ X x.1 x.2) := by
  have hT := fs_deriv_time hX
  have hAv : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : ℝ × Space => fderiv ℝ (X x.1) x.2 x.2) :=
    (fs_fderiv hX).clm_apply contDiff_snd
  have hL := fs_lap hX
  have hXv : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ × Space => X x.1 x.2) := hX
  have h := (((hT.sub (hAv.const_smul (1 / 2 : ℝ))).sub (hL.const_smul ν)).add
    (hXv.const_smul (μ - 1 / 2)))
  exact h

theorem fs_bracket {U X : ℝ → Space → Space}
    (hU : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ × Space => U x.1 x.2))
    (hX : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ × Space => X x.1 x.2)) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ × Space => physBracket (U x.1) (X x.1) x.2) :=
  ((fs_fderiv hX).clm_apply hU).sub ((fs_fderiv hU).clm_apply hX)

theorem fs_cdiff {U X : ℝ → Space → Space}
    (hU : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ × Space => U x.1 x.2))
    (hX : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ × Space => X x.1 x.2)) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : ℝ × Space => physCdiff (U x.1) (X x.1) x.2) := by
  refine ContDiff.sum fun j _ => ContDiff.sum fun l _ => ?_
  exact ((fs_coord l (fs_pd hU j)).smul (fs_pd2 hX j l)).sub
    ((fs_coord l (fs_pd hX j)).smul (fs_pd2 hU j l))

theorem fs_uud2 {U X : ℝ → Space → Space}
    (hU : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ × Space => U x.1 x.2))
    (hX : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ × Space => X x.1 x.2)) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : ℝ × Space => physUUD2 (U x.1) (X x.1) x.2) := by
  refine ContDiff.sum fun j _ => ContDiff.sum fun l _ => ?_
  exact ((fs_coord j hU).mul (fs_coord l hU)).smul (fs_pd2 hX j l)

theorem fs_dxp {X : ℝ → Space → Space} {p : ℝ → Space → ℝ}
    (hX : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ × Space => X x.1 x.2))
    (hp : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ × Space => p x.1 x.2)) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : ℝ × Space => physDXp (X x.1) (p x.1) x.2) := by
  have hq : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : ℝ × Space => fderiv ℝ (p x.1) x.2) := fs_fderiv hp
  have key : ∀ i : Fin 3, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : ℝ × Space => physDXp (X x.1) (p x.1) x.2 i) := by
    intro i
    show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ × Space =>
      ∑ j : Fin 3, (physPd (X x.1) j x.2 i + physPd (X x.1) i x.2 j) *
        fderiv ℝ (p x.1) x.2 (coordinateVector j))
    refine ContDiff.sum fun j _ => ?_
    exact ((fs_coord i (fs_pd hX j)).add (fs_coord j (fs_pd hX i))).mul
      (hq.clm_apply contDiff_const)
  first
    | exact (contDiff_piLp _).2 key
    | exact (contDiff_piLp).2 key
    | exact contDiff_piLp' key

theorem fs_grad {X : ℝ → Space → Space} {p : ℝ → Space → ℝ}
    (hX : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ × Space => X x.1 x.2))
    (hp : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ × Space => p x.1 x.2)) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : ℝ × Space => ∑ j : Fin 3, X x.1 x.2 j * physGrad (p x.1) x.2 j) := by
  refine ContDiff.sum fun j _ => ?_
  exact (fs_coord j hX).mul ((fs_fderiv hp).clm_apply contDiff_const)

theorem fs_residual {ν μ : ℝ} {U X : ℝ → Space → Space} {p : ℝ → Space → ℝ}
    (hU : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ × Space => U x.1 x.2))
    (hX : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ × Space => X x.1 x.2))
    (hp : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ × Space => p x.1 x.2)) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : ℝ × Space => physResidual ν μ U p X x.1 x.2) := by
  have hDm := fs_dmu hX ν (μ + 1)
  have hF := fs_fderiv hDm
  have hA : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : ℝ × Space => fderiv ℝ (physDmu ν (μ + 1) X x.1) x.2 (U x.1 x.2)) :=
    hF.clm_apply hU
  have hC := fs_cdiff hU hX
  have hUU := fs_uud2 hU hX
  have hDXp := fs_dxp hX hp
  have h := (((hA.const_smul (2 : ℝ)).sub (hC.const_smul (2 * ν))).add hUU).sub hDXp
  exact h

theorem wardFieldsSmooth_proved : WardFieldsSmooth := by
  unfold WardFieldsSmooth
  intro ν μ U X p hU hp hX
  exact ⟨fs_bracket hU hX, fs_dmu hX ν (μ + 1), fs_residual hU hX hp, fs_grad hX hp⟩

end UnforcedLeray.Short.PartIIIb.Concrete
