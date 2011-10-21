\begin{flushleft}\ttfamily\upshape\parindent 0pt
and~~\\
is\_{}finite(x)~and~is\_{}finite(y)~~\\
and~no\_{}overflow(f,m,float\_{}value(x)+float\_{}value(y))~$-$>~\\
~~~~is\_{}finite(result)~and~\\
~~~~float\_{}value(result)~=~~\\
~~~~round\_{}float(f,m,float\_{}value(x)+float\_{}value(y))~\\
~~~~and~sign\_{}zero\_{}result(m,result)~\\
and~~\\
is\_{}finite(x)~and~is\_{}finite(y)~~\\
and~not~no\_{}overflow(f,m,float\_{}value(x)+float\_{}value(y))~~\\
$-$>~same\_{}sign\_{}real(result,float\_{}value(x)+float\_{}value(y))~~\\
~~~and~overflow\_{}value(f,m,result)~\\
~~\}~\\
\end{flushleft}