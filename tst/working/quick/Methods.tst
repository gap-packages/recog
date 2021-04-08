#@local f, m

gap> f := x->x;;
gap> m := RecogMethod("yada", "comment", f);
<RecogMethod "yada": function( x ) ... end>
gap> CallRecogMethod(m, [1]);
1
