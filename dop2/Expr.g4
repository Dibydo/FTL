grammar Expr;// (bc)*a

prog:	expr EOF ;

expr: 'bc' expr |
	'a';

NEWLINE : [\r\n]+ -> skip;
