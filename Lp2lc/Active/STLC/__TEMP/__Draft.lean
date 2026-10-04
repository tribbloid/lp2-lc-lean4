

section variable {P : Parameters} {c : P.C}

namespace Labelled -- TODO: this should contains shared abbrev for both AST and Src_, but we don't know how to do this
section variable {Ctor} (this: Labelled Ctor)

abbrev Typ := Ctor .typ
abbrev Trm := Ctor .trm
abbrev Val := Ctor .val

end
end Labelled

end
