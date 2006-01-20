object QuickSort {
    def qsort(xs: List[int]): List[int] = {
        if (xs.length <= 1) { xs }
        else {
            val pivot = xs(xs.length / 2);
                qsort(xs.filter(x => x < pivot))
            :::       xs.filter(x => x == pivot)
            ::: qsort(xs.filter(x => x > pivot))
            
        }
    }
    
    def main(args: Array[String]): unit = {
        System.out.println(qsort(List(2,1,5,3,4)));
    }
}
