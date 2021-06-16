# PrintObj
gap> FindHomMethodsGeneric.TrivialGroup;
<RecogMethod "TrivialGroup": function( ri, G ) ... end>

# Error messages
gap> RecogMethod("", "", "", "", x -> x);
Error, usage: RecogMethod(stamp, comment[, opt], func)
gap> RecogMethod("", "", "", "");
Error, <func> must be a function
gap> RecogMethod("", "", "", x -> x);
Error, <opt> must be a record
gap> UnpackRecogMethod(x -> x);
Error, <m> must be a RecogMethod, but is function ( x )
    return x;
end
gap> CallRecogMethod(x -> x, []);
Error, <m> must be a RecogMethod, but is function ( x )
    return x;
end
