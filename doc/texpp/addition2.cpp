\begin{flushleft}\ttfamily\upshape\parindent 0pt
and~\\
is\_{}finite(x)~and~is\_{}infinite(y)~$-$>~~\\
~~~is\_{}infinite(result)~and~same\_{}sign(result,y)~\\
and~~~~~~~~~~~~~~~~~~~~~\\
is\_{}infinite(x)~and~is\_{}finite(y)~$-$>~\\
~~~is\_{}infinite(result)~and~same\_{}sign(result,x)~\\
and~\\
is\_{}infinite(x)~and~is\_{}infinite(y)~~\\
~~~~~~~~~~~~~~~and~same\_{}sign(x,y)~$-$>~\\
~~~is\_{}infinite(result)~and~same\_{}sign(result,x)~\\
and~\\
is\_{}infinite(x)~and~is\_{}infinite(y)~~\\
~~~~~~~~~~~~~~~and~diff\_{}sign(x,y)~$-$>~is\_{}nan(result)~\\
~\\
~\\
\end{flushleft}