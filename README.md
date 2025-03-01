# Лабораторная работа №4. Лучинкин Константин (SAT-solver for BNN)

## SAT-solver
Задача SAT (satisfability problem) - одна из самых известных задач в computer science. Формулировка задачи относительно простая: дана булевая формула в КНФ, необходимо сообщить выполнима ли она(SAT/UNSAT). Вообще SAT - NP-полная задача, поэтому за полиномиальное время не существует алгоритма способного ее решить. Тем не менее, в силу её большого практического значения современные SAT-solver'ы решают её достаточно быстро. Их основой является алгоритм CDCL. Он и был реализован.
### О практическом применении
>
> SAT is evidently a killer app, because it is key to the solution of so many other problems.
>
> -- <cite> Donald Knuth </cite> 
- Задачи планирования
- Формальная верификация (software/hardware)
- компиляторы
- Задачи оптимизации

### Алгоритм CDCL
[описание алгоритма от его автора](https://www.cs.princeton.edu/~zkincaid/courses/fall18/readings/SATHandbook-CDCL.pdf)

![alt text]({779FF105-27ED-4E27-8CFB-7F6D5ABB9596}.png)

Упрощая CDCL - это алгоритм перепора с очень эффективными эвристиками. 

Первая - это Unit Propagation. Имея клозу с одной переменной, которой не назначили значения можно однозначно определить что она истина(ложна). Это может повлечь появление другой клозы с одной переменной и т.д.

Вторая - Conflict Analysis. Когда перебор натыкается на конфликт (т.е. с текущимм значениями переменных формула невыполнима) можно не просто вернуться на шаг назад, но и извлечь какую-то информацию для дальнейшего использования.

## BNN
BNN - Binary Neural Network. Идея в том, чтобы заменить float веса моделей на 1 или -1, а функции активации на sign(x). Интересно, что такие модели несильно проигрывают в качестве классическим. 

Эта идея позволяет экономить память и вычислительные ресурсы. Это актуально, например, для встроенных систем.
[Здесь можно почитать подробнее](https://arxiv.org/abs/2110.06804)
### BNN to SAT encoding
Подробнее почитать можно [здесь](https://openreview.net/forum?id=SJx-j64FDr) и [здесь](https://rbcborealis.com/research-blogs/tutorial-9-sat-solvers-i-introduction-and-applications/)

В BNN все веса и входные данные - это 1 или -1. Тогда достаточно легко закодировать перемножение. Далее результаты умножения складываются, и вычисляется знак суммы. Нетрудно заметить, что результат будет отрицательным, если хотя бы половина слагаемы отрицательные. Соответствеено нужно уметь кодировать в КНФ условия вида "хотя бы k из n переменных истины". Это назывется boolean cardinality constrains.
### Boolean cardinality constraints
Очевидно мы не можем перебрать все сочетания из n по k, поскольку тогда получиться экспоненциальное количество клоз. К счастью есть способы получить полиномиальное количество. Я реализовал по [этой](https://www.cs.toronto.edu/~fbacchus/csc2512/Assignments/Bailleux-Boufkhad2003_Chapter_EfficientCNFEncodingOfBooleanC.pdf) статье. 

## Источники
Помимо того, что уже упомянуто:
- [доклад на Clojure conf](https://www.youtube.com/watch?v=d76e4hV1iJY&t=1437s)
- [Carsten Sinz: Towards an Optimal CNF Encoding of
Boolean Cardinality Constraints]()
- [Alexander Kulikov - The Satisfability Problem](https://www.youtube.com/watch?v=4K1MyG4ljI8&t=500s)
- [Александр Андреев - Алгоритмы решения SAT: теоретические и практические аспекты](https://www.youtube.com/watch?v=s8jbd_R8fcA)