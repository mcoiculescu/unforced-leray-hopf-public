import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_3_3_1_dec

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open MeasureTheory
open scoped ENNReal
open UnforcedLeray.Cyl
open UnforcedLeray.TrainB

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

local instance : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩

/-- The centered-cell L² class of a classical cylinder derivative word (general `k`; the
`k = 3` version is `TrainB.smoothWordCell`). -/
private noncomputable def smoothWordCellS1 {c : ℝ} (u : Plane → Vec2)
    (hu : Sob.IsCylSmooth c u) (vs : List Plane) : L2v c := by
  let hm := (hu.iterD vs).memLp (Cyl.ρwW c ^ (0 : ℝ)) 2
  let hMP : MeasurePreserving id (cellμ c)
      (Sob.wμ (Sob.cylinder c).μ (Cyl.ρwW c ^ (0 : ℝ))) := by
    rw [← vecH1_measure_eq_cell c]
    exact MeasurePreserving.id _
  exact Lp.compMeasurePreserving id hMP (hm.toLp (Sob.iterD vs u))

private theorem smoothWordCellS1_ae {c : ℝ} (u : Plane → Vec2)
    (hu : Sob.IsCylSmooth c u) (vs : List Plane) :
    (smoothWordCellS1 u hu vs : Plane → Vec2) =ᵐ[cellμ c] Sob.iterD vs u := by
  let hm := (hu.iterD vs).memLp (Cyl.ρwW c ^ (0 : ℝ)) 2
  have hMP : MeasurePreserving id (cellμ c)
      (Sob.wμ (Sob.cylinder c).μ (Cyl.ρwW c ^ (0 : ℝ))) := by
    rw [← vecH1_measure_eq_cell c]
    exact MeasurePreserving.id _
  have hcomp := Lp.coeFn_compMeasurePreserving (hm.toLp (Sob.iterD vs u)) hMP
  have hcoe : (hm.toLp (Sob.iterD vs u) : Plane → Vec2) =ᵐ[cellμ c] Sob.iterD vs u := by
    exact hMP.quasiMeasurePreserving.ae hm.coeFn_toLp
  filter_upwards [hcomp, hcoe] with z hz₁ hz₂
  change ((Lp.compMeasurePreserving id hMP (hm.toLp (Sob.iterD vs u)) : L2v c) : Plane → Vec2) z = _
  simpa [smoothWordCellS1, Function.comp_id] using hz₁.trans hz₂

private theorem smoothWordCellS1_memLp {c : ℝ} (u : Plane → Vec2)
    (hu : Sob.IsCylSmooth c u) (vs : List Plane) :
    MemLp (smoothWordCellS1 u hu vs : Plane → Vec2) 2 (cellμ c) := by
  exact Lp.memLp (smoothWordCellS1 u hu vs)

/-- The single-step projected `q`-derivative of a smooth classical word. -/
private theorem projQS1 {c : ℝ} (hc : 0 < c)
    (u : Plane → Vec2) (hu : Sob.IsCylSmooth c u) (vs : List Plane) :
    Sob.HasWeakDeriv (Sob.cylinder c) [((1 : ℝ), (0 : ℝ))]
      (Cyl.P0 c (smoothWordCellS1 u hu vs) : Plane → Vec2)
      (Cyl.P0 c (smoothWordCellS1 u hu ((1, 0) :: vs)) : Plane → Vec2) := by
  let x : VecH1 c := Sob.W.ofCylSmooth (ρ := Cyl.ρwW c ^ (0 : ℝ))
    (𝕜 := ℝ) (F := Vec2) (k := 1) (p := 2) hc (Sob.iterD vs u) (hu.iterD vs)
  have hval : vecH1ValueCellCLM_MP x = smoothWordCellS1 u hu vs := by
    apply Lp.ext
    have h := vecH1ValueCellCLM_MP_ofCylSmooth_ae hc (hu.iterD vs)
    have hcoe := smoothWordCellS1_ae u hu vs
    filter_upwards [h, hcoe] with z hz₁ hz₂
    exact hz₁.trans hz₂.symm
  have hq : vecH1DqCellCLM_MP x = smoothWordCellS1 u hu ((1, 0) :: vs) := by
    apply Lp.ext
    have h := vecH1DqCellCLM_MP_ofCylSmooth_ae hc (hu.iterD vs)
    have hcoe := smoothWordCellS1_ae u hu ((1, 0) :: vs)
    have hword : Cyl.partialQ (Sob.iterD vs u) = Sob.iterD ((1, 0) :: vs) u := by
      funext z
      simp only [Sob.iterD_cons]
      exact (Cyl.partialQ_eq_fderiv ((hu.iterD vs).smooth.differentiable (by simp)) z)
    filter_upwards [h, hcoe] with z hz₁ hz₂
    exact hz₁.trans ((congrFun hword z).trans hz₂.symm)
  have hw := hasWeakDeriv_P0_q_of_vecH1 hc x
  have hsource : (Cyl.P0 c (vecH1ValueCellCLM_MP x) : Plane → Vec2) =ᵐ[cellμ c]
      (Cyl.P0 c (smoothWordCellS1 u hu vs) : Plane → Vec2) := by
    rw [hval]
  have htarget : (Cyl.P0 c (vecH1DqCellCLM_MP x) : Plane → Vec2) =ᵐ[cellμ c]
      (Cyl.P0 c (smoothWordCellS1 u hu ((1, 0) :: vs)) : Plane → Vec2) := by
    rw [hq]
  have hcell : MeasurePreserving id (Sob.cylinder c).μ (cellμ c) := by
    rw [Cyl.cylinder_μ_eq]
    exact MeasurePreserving.id _
  have hsource' : (Cyl.P0 c (vecH1ValueCellCLM_MP x) : Plane → Vec2) =ᵐ[
      (Sob.cylinder c).μ] (Cyl.P0 c (smoothWordCellS1 u hu vs) : Plane → Vec2) := by
    exact hcell.quasiMeasurePreserving.ae hsource
  have htarget' : (Cyl.P0 c (vecH1DqCellCLM_MP x) : Plane → Vec2) =ᵐ[
      (Sob.cylinder c).μ] (Cyl.P0 c (smoothWordCellS1 u hu ((1, 0) :: vs)) : Plane → Vec2) := by
    exact hcell.quasiMeasurePreserving.ae htarget
  exact hw.congr_ae hsource' htarget'

private theorem projES1 {c : ℝ} (hc : 0 < c)
    (u : Plane → Vec2) (hu : Sob.IsCylSmooth c u) (vs : List Plane) :
    Sob.HasWeakDeriv (Sob.cylinder c) [((0 : ℝ), (1 : ℝ))]
      (Cyl.P0 c (smoothWordCellS1 u hu vs) : Plane → Vec2)
      (Cyl.P0 c (smoothWordCellS1 u hu ((0, 1) :: vs)) : Plane → Vec2) := by
  let x : VecH1 c := Sob.W.ofCylSmooth (ρ := Cyl.ρwW c ^ (0 : ℝ))
    (𝕜 := ℝ) (F := Vec2) (k := 1) (p := 2) hc (Sob.iterD vs u) (hu.iterD vs)
  have hval : vecH1ValueCellCLM_MP x = smoothWordCellS1 u hu vs := by
    apply Lp.ext
    have h := vecH1ValueCellCLM_MP_ofCylSmooth_ae hc (hu.iterD vs)
    have hcoe := smoothWordCellS1_ae u hu vs
    filter_upwards [h, hcoe] with z hz₁ hz₂
    exact hz₁.trans hz₂.symm
  have he : vecH1DetaCellCLM_MP x = smoothWordCellS1 u hu ((0, 1) :: vs) := by
    apply Lp.ext
    have h := vecH1DetaCellCLM_MP_ofCylSmooth_ae hc (hu.iterD vs)
    have hcoe := smoothWordCellS1_ae u hu ((0, 1) :: vs)
    have hword : Cyl.partialEta (Sob.iterD vs u) = Sob.iterD ((0, 1) :: vs) u := by
      funext z
      simp only [Sob.iterD_cons]
      exact (Cyl.partialEta_eq_fderiv ((hu.iterD vs).smooth.differentiable (by simp)) z)
    filter_upwards [h, hcoe] with z hz₁ hz₂
    exact hz₁.trans ((congrFun hword z).trans hz₂.symm)
  have hw := hasWeakDeriv_P0_eta_of_vecH1 hc x
  have hsource : (Cyl.P0 c (vecH1ValueCellCLM_MP x) : Plane → Vec2) =ᵐ[cellμ c]
      (Cyl.P0 c (smoothWordCellS1 u hu vs) : Plane → Vec2) := by rw [hval]
  have htarget : (Cyl.P0 c (vecH1DetaCellCLM_MP x) : Plane → Vec2) =ᵐ[cellμ c]
      (Cyl.P0 c (smoothWordCellS1 u hu ((0, 1) :: vs)) : Plane → Vec2) := by rw [he]
  have hcell : MeasurePreserving id (Sob.cylinder c).μ (cellμ c) := by
    rw [Cyl.cylinder_μ_eq]
    exact MeasurePreserving.id _
  have hsource' : (Cyl.P0 c (vecH1ValueCellCLM_MP x) : Plane → Vec2) =ᵐ[
      (Sob.cylinder c).μ] (Cyl.P0 c (smoothWordCellS1 u hu vs) : Plane → Vec2) :=
    hcell.quasiMeasurePreserving.ae hsource
  have htarget' : (Cyl.P0 c (vecH1DetaCellCLM_MP x) : Plane → Vec2) =ᵐ[
      (Sob.cylinder c).μ] (Cyl.P0 c (smoothWordCellS1 u hu ((0, 1) :: vs)) : Plane → Vec2) :=
    hcell.quasiMeasurePreserving.ae htarget
  exact hw.congr_ae hsource' htarget'

private theorem projWeakS1 {c : ℝ} (hc : 0 < c)
    (u : Plane → Vec2) (hu : Sob.IsCylSmooth c u) :
    ∀ vs : List Plane,
      (∀ v ∈ vs, v = (1, 0) ∨ v = (0, 1)) →
      Sob.HasWeakDeriv (Sob.cylinder c) vs
        (Cyl.P0 c (smoothWordCellS1 u hu []) : Plane → Vec2)
        (Cyl.P0 c (smoothWordCellS1 u hu vs) : Plane → Vec2) := by
  intro vs
  induction vs with
  | nil =>
      intro _
      apply Sob.HasWeakDeriv.nil
      intro φ hφ
      exact Sob.integrable_smul_of_memLp (p := 2) (Sob.CompactlyBounded.of_adm hφ)
        (memLp_cell_to_weighted (Cyl.P0 c (smoothWordCellS1 u hu [])))
  | cons v vs ih =>
      intro hvs
      have hv := hvs v (by simp)
      have hrest : ∀ w ∈ vs, w = (1, 0) ∨ w = (0, 1) := by
        intro w hw
        exact hvs w (by simp [hw])
      have htail := ih hrest
      have hsingle : Sob.HasWeakDeriv (Sob.cylinder c) [v]
          (Cyl.P0 c (smoothWordCellS1 u hu vs) : Plane → Vec2)
          (Cyl.P0 c (smoothWordCellS1 u hu (v :: vs)) : Plane → Vec2) := by
        rcases hv with hq | he
        · rw [hq]
          simpa using projQS1 hc u hu vs
        · rw [he]
          simpa using projES1 hc u hu vs
      exact htail.cons hsingle

private noncomputable def projWordS1 {c : ℝ} {k : ℕ} (u : Plane → Vec2)
    (hu : Sob.IsCylSmooth c u) (α : Sob.Idx 2 k) : L2v c :=
  Cyl.P0 c (smoothWordCellS1 u hu ((Sob.cylinder c).word α))

private theorem projWordS1_memLp_weighted {c : ℝ} {k : ℕ} (u : Plane → Vec2)
    (hu : Sob.IsCylSmooth c u) (α : Sob.Idx 2 k) :
    MemLp (projWordS1 u hu α : Plane → Vec2) 2
      (Sob.wμ (Sob.cylinder c).μ (Cyl.ρwW c ^ (0 : ℝ))) :=
  memLp_cell_to_weighted (projWordS1 u hu α)

/-- **Sub1 for all orders** (`P0SmoothRegK`).  For a smooth `c`-periodic field `u` vanishing for
large `|η|`, and every `k`, the class `P₀ u` is the value component of an element of the
unweighted `H^k(cell; ℝ²)`.  Construction: the components of `y` are the projected words
`P₀ (∂^α u)`, which are weak derivatives of each other by the `k`-general version of the
`H³` argument (`projWeakS1`), and `value y = P₀ (∂^∅ u) = P₀ u` on the cell. -/
theorem p0SmoothRegK : P0SmoothRegK := by
  intro c hc u hu k
  let g : Sob.Idx 2 k → Plane → Vec2 := fun α z => (projWordS1 u hu α : Plane → Vec2) z
  have hmem : ∀ α : Sob.Idx 2 k,
      MemLp (g α) 2 (Sob.wμ (Sob.cylinder c).μ (Cyl.ρwW c ^ (0 : ℝ))) := by
    intro α
    exact projWordS1_memLp_weighted u hu α
  have hdirs (α : Sob.Idx 2 k) : ∀ v ∈ (Sob.cylinder c).word α,
      v = (1, 0) ∨ v = (0, 1) := by
    intro v hv
    simp only [Sob.TestDomain.word, List.mem_ofFn] at hv
    rcases hv with ⟨i, hi⟩
    generalize hidx : α.2 i = j at hi
    change Sob.cylDir j = v at hi
    fin_cases j
    · left
      simpa [Sob.cylDir] using hi.symm
    · right
      simpa [Sob.cylDir] using hi.symm
  have hweak : ∀ α : Sob.Idx 2 k,
      Sob.HasWeakDeriv (Sob.cylinder c) ((Sob.cylinder c).word α)
        (g Sob.Idx.zero) (g α) := by
    intro α
    have h := projWeakS1 hc u hu ((Sob.cylinder c).word α) (hdirs α)
    simpa [g, projWordS1, Sob.TestDomain.word_zero] using h
  let y : UnforcedLeray.Cyl.H ℝ Vec2 c 0 k := Sob.W.ofFields
    (D := Sob.cylinder c) (ρ := Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ) (F := Vec2)
    (k := k) (p := 2) g hmem hweak
  refine ⟨y, ?_⟩
  have hMP : MeasurePreserving id (cellμ c)
      (Sob.wμ (Sob.cylinder c).μ (Cyl.ρwW c ^ (0 : ℝ))) := by
    rw [← vecH1_measure_eq_cell c]
    exact MeasurePreserving.id _
  -- the value of `y` is the zero-th component, which is `g 0` a.e.
  have hyv : Sob.W.value _ _ _ _ _ _ y = (hmem Sob.Idx.zero).toLp (g Sob.Idx.zero) := rfl
  have hval : (Sob.W.value _ _ _ _ _ _ y : Plane → Vec2) =ᵐ[cellμ c] (g Sob.Idx.zero) := by
    have h1 : (Sob.W.value _ _ _ _ _ _ y : Plane → Vec2) =ᵐ[
        Sob.wμ (Sob.cylinder c).μ (Cyl.ρwW c ^ (0 : ℝ))] (g Sob.Idx.zero) := by
      rw [hyv]
      exact (hmem Sob.Idx.zero).coeFn_toLp
    exact hMP.quasiMeasurePreserving.ae h1
  -- the zero-th component is `P₀` of the class of `u`
  have hsm : MemLp u 2 (cellμ c) := by
    refine MemLp.ae_eq ?_ (smoothWordCellS1_memLp u hu [])
    filter_upwards [smoothWordCellS1_ae u hu []] with z hz
    rw [hz, Sob.iterD_nil]
  have hL : UnforcedLeray.Short.IIIa.toL2v c u = smoothWordCellS1 u hu [] := by
    unfold UnforcedLeray.Short.IIIa.toL2v
    rw [dif_pos hsm]
    apply Lp.ext
    filter_upwards [hsm.coeFn_toLp, smoothWordCellS1_ae u hu []] with z h1 h2
    rw [Sob.iterD_nil] at h2
    rw [h1]
    exact h2.symm
  have hfun : g Sob.Idx.zero
      = (Cyl.P0 c (smoothWordCellS1 u hu []) : Plane → Vec2) := by
    have hg0 : g Sob.Idx.zero = (projWordS1 u hu Sob.Idx.zero : Plane → Vec2) := rfl
    have hw : (Sob.cylinder c).word (Sob.Idx.zero : Sob.Idx 2 k) = [] := rfl
    have hpw : projWordS1 u hu (Sob.Idx.zero : Sob.Idx 2 k)
        = Cyl.P0 c (smoothWordCellS1 u hu []) := by
      unfold projWordS1
      rw [hw]
    rw [hg0, hpw]
  rw [hL]
  exact hval.trans (Filter.Eventually.of_forall (fun z => congrFun hfun z))

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
