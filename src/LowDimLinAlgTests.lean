module

import LSpec
import LowDimLinAlg

open LSpec

namespace LowDimLinAlgTests

/- ... -/

end LowDimLinAlgTests

public def main : List String → IO UInt32 :=
  lspecIO ∘ Std.HashMap.ofList ∘ List.map (Prod.map id List.singleton) <| []
