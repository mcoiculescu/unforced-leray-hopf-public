import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T22_2_3_1.Route

/-!


Source of record: `the November 2 reference manuscript` lines 2100-2105 (the
backward solution behind the duality argument must be `C^∞` jointly: `BwdSol.smooth`,
`CylEtaTest` of `Sub/T22_2.lean`).  The source treats this as standard; the file records the pure
calculus: iterated partials along words, jointly smooth coefficients `JSmooth`, time derivatives
`HasTimeDeriv`, and the closure of `SpSmooth` under `∂_j`, sums and multiplication by jointly
smooth coefficients.  No heat kernel enters.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.IIb.BwdRoute.Joint

open CylPDE

/-- A jointly smooth coefficient on `[0, T] × ℝ²`. -/
def JSmooth (T : ℝ) (a : ℝ → Pl → ℝ) : Prop :=
  ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : ℝ × Pl => a z.1 z.2) (Icc 0 T ×ˢ univ)

/-- `h` is the time derivative of `g` on `[0, T]`, one-sided at the ends. -/
def HasTimeDeriv (T : ℝ) (g h : ℝ → Pl → ℝ) : Prop :=
  ∀ s ∈ Icc 0 T, ∀ x : Pl, HasDerivWithinAt (fun r => g r x) (h s x) (Icc 0 T) s

/-- A tower of successive time derivatives inside the class `SpSmooth`. -/
structure Tower (T : ℝ) (D : ℕ → ℝ → Pl → ℝ) : Prop where
  sp : ∀ j, SpSmooth T (D j)
  dt : ∀ j, HasTimeDeriv T (D j) (D (j + 1))

/-! ## Words -/

theorem pdW_append (l m : List (Fin 2)) (g : Pl → ℝ) : pdW (l ++ m) g = pdW l (pdW m g) := by
  induction l with
  | nil => rfl
  | cons j l ih => simp only [List.cons_append, pdW, ih]

theorem pdW_concat (l : List (Fin 2)) (j : Fin 2) (g : Pl → ℝ) :
    pdW (l ++ [j]) g = pdW l (B0579.pd j g) :=
  pdW_append l [j] g

theorem contDiff_pd (j : Fin 2) {g : Pl → ℝ} (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (B0579.pd j g) :=
  ((contDiff_infty_iff_fderiv.1 hg).2).clm_apply contDiff_const

theorem contDiff_pdW (l : List (Fin 2)) {g : Pl → ℝ}
    (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (pdW l g) := by
  induction l with
  | nil => exact hg
  | cons j l ih => exact contDiff_pd j ih

theorem pd_add_fun (j : Fin 2) {f g : Pl → ℝ} (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) :
    B0579.pd j (fun x => f x + g x) = fun x => B0579.pd j f x + B0579.pd j g x := by
  funext x
  simp only [B0579.pd]
  rw [fderiv_fun_add (hf x) (hg x)]
  rfl

theorem pdW_add (l : List (Fin 2)) {f g : Pl → ℝ}
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g) :
    pdW l (fun x => f x + g x) = fun x => pdW l f x + pdW l g x := by
  induction l with
  | nil => rfl
  | cons j l ih =>
    simp only [pdW, ih]
    exact pd_add_fun j ((contDiff_pdW l hf).differentiable (by simp))
      ((contDiff_pdW l hg).differentiable (by simp))

/-! ## `SpSmooth` under `∂_j` and sums -/

theorem spSmooth_pd {T : ℝ} {g : ℝ → Pl → ℝ} (hg : SpSmooth T g) (j : Fin 2) :
    SpSmooth T (fun s => B0579.pd j (g s)) := by
  refine ⟨fun σ hσ => contDiff_pd j (hg.slice σ hσ), fun l => ?_⟩
  have h := hg.cont (l ++ [j])
  simpa only [pdW_concat] using h

theorem spSmooth_add {T : ℝ} {g h : ℝ → Pl → ℝ} (hg : SpSmooth T g) (hh : SpSmooth T h) :
    SpSmooth T (fun s x => g s x + h s x) := by
  refine ⟨fun σ hσ => (hg.slice σ hσ).add (hh.slice σ hσ), fun l => ?_⟩
  refine ((hg.cont l).add (hh.cont l)).congr ?_
  rintro z ⟨hz, -⟩
  show pdW l (fun x => g z.1 x + h z.1 x) z.2 = _
  rw [pdW_add l (hg.slice _ hz) (hh.slice _ hz)]
  rfl

/-! ## Jointly smooth coefficients -/

section JSmooth

variable {T : ℝ} {a : ℝ → Pl → ℝ}

theorem uniqueDiffOn_dom (hT : 0 < T) : UniqueDiffOn ℝ (Icc 0 T ×ˢ (univ : Set Pl)) :=
  (uniqueDiffOn_Icc hT).prod uniqueDiffOn_univ

theorem JSmooth.continuousOn (ha : JSmooth T a) :
    ContinuousOn (fun z : ℝ × Pl => a z.1 z.2) (Icc 0 T ×ˢ univ) :=
  ContDiffOn.continuousOn ha

theorem JSmooth.slice (ha : JSmooth T a) {s : ℝ} (hs : s ∈ Icc 0 T) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (a s) := by
  have hm : MapsTo (fun x : Pl => ((s, x) : ℝ × Pl)) univ (Icc 0 T ×ˢ univ) :=
    fun x _ => ⟨hs, mem_univ _⟩
  have h : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : Pl => a s x) univ :=
    ContDiffOn.comp (g := fun z : ℝ × Pl => a z.1 z.2) ha
      (contDiff_const.prodMk contDiff_id).contDiffOn hm
  exact contDiffOn_univ.1 h

/-- The full derivative of a jointly smooth coefficient within the closed domain. -/
theorem JSmooth.hasFDerivWithinAt (ha : JSmooth T a) {z : ℝ × Pl}
    (hz : z ∈ Icc 0 T ×ˢ (univ : Set Pl)) :
    HasFDerivWithinAt (fun z : ℝ × Pl => a z.1 z.2)
      (fderivWithin ℝ (fun z : ℝ × Pl => a z.1 z.2) (Icc 0 T ×ˢ univ) z) (Icc 0 T ×ˢ univ) z :=
  (ContDiffOn.differentiableOn ha (by simp) z hz).hasFDerivWithinAt

/-- A direction of the full derivative is again jointly smooth. -/
theorem JSmooth.fderivWithin_apply (hT : 0 < T) (ha : JSmooth T a) (v : ℝ × Pl) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : ℝ × Pl => fderivWithin ℝ (fun z : ℝ × Pl => a z.1 z.2) (Icc 0 T ×ˢ univ) z v)
      (Icc 0 T ×ˢ univ) := by
  have h : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fderivWithin ℝ (fun z : ℝ × Pl => a z.1 z.2) (Icc 0 T ×ˢ univ)) (Icc 0 T ×ˢ univ) :=
    ContDiffOn.fderivWithin ha (uniqueDiffOn_dom hT) (by simp)
  exact h.clm_apply contDiffOn_const

theorem JSmooth.pd_eq (ha : JSmooth T a) {s : ℝ} (hs : s ∈ Icc 0 T) (j : Fin 2) (x : Pl) :
    B0579.pd j (a s) x =
      fderivWithin ℝ (fun z : ℝ × Pl => a z.1 z.2) (Icc 0 T ×ˢ univ) (s, x) (0, B0579.dir j) := by
  have h1 := ha.hasFDerivWithinAt (z := (s, x)) ⟨hs, mem_univ _⟩
  have hι : HasFDerivWithinAt (fun y : Pl => ((s, y) : ℝ × Pl))
      (ContinuousLinearMap.inr ℝ ℝ Pl) univ x := (hasFDerivAt_prodMk_right s x).hasFDerivWithinAt
  have h2 := h1.comp x hι (fun y _ => ⟨hs, mem_univ y⟩)
  have h3 : HasFDerivAt (a s) ((fderivWithin ℝ (fun z : ℝ × Pl => a z.1 z.2) (Icc 0 T ×ˢ univ)
      (s, x)).comp (ContinuousLinearMap.inr ℝ ℝ Pl)) x := hasFDerivWithinAt_univ.1 h2
  simp only [B0579.pd]
  rw [h3.fderiv]
  simp

/-- Spatial partials of a jointly smooth coefficient are jointly smooth. -/
theorem JSmooth.pd (hT : 0 < T) (ha : JSmooth T a) (j : Fin 2) :
    JSmooth T (fun s => B0579.pd j (a s)) := by
  refine (ha.fderivWithin_apply hT (0, B0579.dir j)).congr ?_
  rintro z ⟨hz, -⟩
  exact ha.pd_eq hz j z.2

/-- The time derivative of a jointly smooth coefficient. -/
def dtJ (T : ℝ) (a : ℝ → Pl → ℝ) : ℝ → Pl → ℝ :=
  fun s x => fderivWithin ℝ (fun z : ℝ × Pl => a z.1 z.2) (Icc 0 T ×ˢ univ) (s, x) (1, 0)

theorem JSmooth.dtJ_smooth (hT : 0 < T) (ha : JSmooth T a) : JSmooth T (dtJ T a) :=
  ha.fderivWithin_apply hT (1, 0)

theorem JSmooth.hasTimeDeriv (ha : JSmooth T a) : HasTimeDeriv T a (dtJ T a) := by
  intro s hs x
  have h1 := ha.hasFDerivWithinAt (z := (s, x)) ⟨hs, mem_univ _⟩
  have hc : HasDerivWithinAt (fun r : ℝ => ((r, x) : ℝ × Pl)) ((1 : ℝ), (0 : Pl)) (Icc 0 T) s :=
    ((hasDerivAt_id s).prodMk (hasDerivAt_const s x)).hasDerivWithinAt
  have hm : MapsTo (fun r : ℝ => ((r, x) : ℝ × Pl)) (Icc 0 T) (Icc 0 T ×ˢ univ) :=
    fun r hr => ⟨hr, mem_univ _⟩
  exact h1.comp_hasDerivWithinAt (x := s) hc hm

theorem jSmooth_const (T c : ℝ) : JSmooth T (fun _ _ => c) := contDiffOn_const

theorem JSmooth.neg (ha : JSmooth T a) : JSmooth T (fun s x => -a s x) :=
  ContDiffOn.neg ha

/-- The components of a jointly smooth drift. -/
theorem jSmooth_comp {w : ℝ → Pl → UnforcedLeray.Train.Vec}
    (hw : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : ℝ × Pl => w z.1 z.2) (Icc 0 T ×ˢ univ))
    (i : Fin 2) : JSmooth T (fun s x => w s x i) :=
  (EuclideanSpace.proj i : UnforcedLeray.Train.Vec →L[ℝ] ℝ).contDiff.comp_contDiffOn hw

end JSmooth

/-! ## `SpSmooth` under multiplication by jointly smooth coefficients -/

theorem spSmooth_mul_cont {T : ℝ} (hT : 0 < T) : ∀ (n : ℕ) (l : List (Fin 2)), l.length = n →
    ∀ (a g : ℝ → Pl → ℝ), JSmooth T a → SpSmooth T g →
    ContinuousOn (fun z : ℝ × Pl => pdW l (fun x => a z.1 x * g z.1 x) z.2)
      (Icc 0 T ×ˢ univ) := by
  intro n
  induction n with
  | zero =>
    intro l hl a g ha hg
    obtain rfl := List.length_eq_zero_iff.1 hl
    exact ha.continuousOn.mul (hg.cont [])
  | succ n ih =>
    intro l hl a g ha hg
    obtain ⟨l', j, rfl⟩ : ∃ l' j, l = l' ++ [j] := by
      rcases List.eq_nil_or_concat' l with rfl | h
      · simp at hl
      · exact h
    have hl' : l'.length = n := by simpa using hl
    have h1 := ih l' hl' (fun s => B0579.pd j (a s)) g (ha.pd hT j) hg
    have h2 := ih l' hl' a (fun s => B0579.pd j (g s)) ha (spSmooth_pd hg j)
    refine (h1.add h2).congr ?_
    rintro z ⟨hz, -⟩
    have hA := ha.slice hz
    have hG := hg.slice _ hz
    show pdW (l' ++ [j]) _ z.2 = _
    rw [pdW_concat]
    have e : B0579.pd j (fun x => a z.1 x * g z.1 x) =
        fun x => B0579.pd j (a z.1) x * g z.1 x + a z.1 x * B0579.pd j (g z.1) x := by
      funext x
      exact B0579.pd_mul (hA.differentiable (by simp)) (hG.differentiable (by simp)) j x
    rw [e, pdW_add l' ((contDiff_pd j hA).mul hG) (hA.mul (contDiff_pd j hG))]
    rfl

theorem spSmooth_mul {T : ℝ} (hT : 0 < T) {a g : ℝ → Pl → ℝ} (ha : JSmooth T a)
    (hg : SpSmooth T g) : SpSmooth T (fun s x => a s x * g s x) :=
  ⟨fun σ hσ => (ha.slice hσ).mul (hg.slice σ hσ),
    fun l => spSmooth_mul_cont hT _ l rfl a g ha hg⟩

end UnforcedLeray.Short.IIb.BwdRoute.Joint
