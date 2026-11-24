import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_9_1

/-!
# `PartIII-b:C/asrc/ra/9/2` : decomposition of `rAGeoConv` (source 5040-5044, 2076-2077)

Same split as `PartIII-b_C_asrc_ra_9_1`: support/measurability and the cell `L²` bound of the
chart remainder of `div(U_raw⊗ĥ_A + ĥ_A⊗U_raw)`.
Source of record: `the November 2 reference manuscript` (73 pages).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **Lemma 1** (measurability and support of the convection piece). -/
def GeoConvMeas (as : ℝ) (χf : ℝ → ℝ) : Prop :=
  GeoPieceMeas as χf (fun p μ A => geoConvPiece p μ χf A)

/-- **Lemma 2** (cell `L²` bound of the convection chart remainder, source 5040-5044). -/
def GeoConvL2 (as : ℝ) (χf : ℝ → ℝ) : Prop :=
  GeoPieceL2 as χf (fun p μ A => geoConvPiece p μ χf A)

theorem rAGeoConv_of (as : ℝ) (χf : ℝ → ℝ) (h1 : GeoConvMeas as χf) (h2 : GeoConvL2 as χf) :
    RAGeoConvLeaf as χf :=
  raGeoPieceBound_of h1 h2

end UnforcedLeray.Short.PartIIIb.Concrete
