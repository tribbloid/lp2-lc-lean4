import «ContextualEmbedding».CE

namespace ContextualEmbedding.CE

open STLCCtx

def binaryReturnsFirst : STLCCtx ts (a :-> b :-> a) :=
  CLam (fun x => CLam (fun _y => CVar x))

#check binaryReturnsFirst

end ContextualEmbedding.CE
