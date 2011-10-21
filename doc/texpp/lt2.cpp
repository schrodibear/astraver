\begin{flushleft}\ttfamily\upshape\parindent 0pt
and~\\
is\_{}infinite(x)~and~is\_{}infinite(y)~$-$>~~\\
~~\textbf{if}~result~then~~\\
~~~~~~~~~~~~float\_{}sign(x)~=~Negative~and~~\\
~~~~~~~~~~~~float\_{}sign(y)~=~Positive~\\
~~\textbf{else}~float\_{}sign(x)~=~Positive~or~~\\
~~~~~~~float\_{}sign(y)~=~Negative~~\\
and~\\
is\_{}finite(x)~and~is\_{}finite(y)~$-$>~~\\
~~\textbf{if}~result~then~~\\
~~~~~~~~~~~~float\_{}value(x)~<~float\_{}value(y)~\\
~~\textbf{else}~float\_{}value(x)~>=~float\_{}value(y)~\\
\end{flushleft}