for fn in good good1 good2 good3 bad1 bad2
    echo $fn
    synquid lifty --print-stats --verify --only=$fn --file=Test.sq --libs=../Prelude.sq --libs=../Tagged.sq > out/$fn.out 2>&1
  end  

for fn in *.sq
    if test "$fn" != "Test.sq"
      echo $fn
      synquid lifty --print-stats --verify --file=$fn --libs=../Prelude.sq --libs=../Tagged.sq > out/$fn.out 2>&1
    end
  end