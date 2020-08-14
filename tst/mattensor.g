# MatTensor:
# Usage: ReadPackage("recog","tst/MatTensor.g");
LoadPackage("recog");
ReadPackage("recog","tst/products.g");
sl := SL(8,3);
gl := GL(8,3);
sp := Sp(8,3);
slxsp := TensorProductOfMatrixGroup(sl,sp);
glxsp := TensorProductOfMatrixGroup(gl,sp);
Print("Testing MatTensor1:\n");
rislxsp := RECOG.TestGroup(slxsp,false,Size(sl)*Size(sp)/2);
Print("\n");
Print("Testing MatTensor2:\n");
rislxsp := RECOG.TestGroup(glxsp,false,Size(gl)*Size(sp)/2);
Print("\n");
sl := SL(10,3);
gl := GL(10,3);
sp := Sp(12,3);
slxsp := TensorProductOfMatrixGroup(sl,sp);
glxsp := TensorProductOfMatrixGroup(gl,sp);
Print("Testing MatTensor3:\n");
rislxsp := RECOG.TestGroup(slxsp,false,Size(sl)*Size(sp)/2);
Print("\n");
Print("Testing MatTensor4:\n");
rislxsp := RECOG.TestGroup(glxsp,false,Size(gl)*Size(sp)/2);
Print("\n");

