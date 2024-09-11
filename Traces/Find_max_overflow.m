load "Crypto/General.m";
error_poly := Read("poly.txt");
list := [Z | ];
for str in Split(error_poly, "+") do
    ind := Index(str, "x");
    nmb := (ind gt 0) select StringToInteger(str[1..ind - 1], 16) else StringToInteger(str, 16);
    Append(~list, Abs(CenteredReduction(nmb, p)));
end for;
max := Maximum(list);
"Maximum value of overflow", max;