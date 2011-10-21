\begin{flushleft}\ttfamily\upshape\parindent 0pt
~\\
Record~gen\_{}float~:~Set~:=~mk\_{}gen\_{}float~\{~\\
~~~genf~:~float2;~\\
~~~float\_{}class~:~Float\_{}class;~\\
~~~float\_{}sign~:~sign;~\\
~~~sign\_{}invariant:~float\_{}class~=~Finite~$-$>~~\\
~~~~~~(float2R~genf~<>~0)\%{}R~$-$>~\\
~~~~~~~same\_{}sign\_{}real\_{}bool~float\_{}sign~(float2R~genf);~\\
~~~float\_{}value~:=~float2R~genf;~\\
~~~exact\_{}value~:~R;~\\
~~~model\_{}value~:~R~\\
\}.~\\
\end{flushleft}