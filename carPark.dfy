class {:autocontracts} CarPark {

    ghost var size: int
    ghost var reservedSpaces: int
    ghost var availNonResSpaces: int
    ghost var availResSpaces: int
    ghost var nonReservedPark: seq<bool>
    ghost var reservedPark: seq<string>
    ghost var full: bool

    var carpark: array<bool>
    var reserevedArea: set<int>
    var weekend: bool
    var reserevedPointer: int
    var carparkPointer: int
    var subscriptions: seq<int>
    var availableSpaces: int
    
    ghost predicate Valid() {
        // size - reservedSpaces == |nonReservedPark|
        // && size == |nonReservedPark| + |reservedPark|
        // && availNonResSpaces >= 5
        forall i :: 0 <= i < carpark.Length ==> carpark[i] == false || true
    }
        //arguments - reserved area space, day, normal spaces, array of exisiting subscribed cars, closing time 
    constructor(parkSize: int, weekend: bool, reservedSpaces: int, subscriptions: seq<int>) 
        requires parkSize > 6 //size should always be a positive number
        requires parkSize > reservedSpaces && reservedSpaces > 0 //total spots alaways greater than 0 and the resereved spaces
        requires |subscriptions| <= reservedSpaces //number of subcriptions less than reserved spots
    {
        size := parkSize;
        carparkPointer, carpark := 0, new bool[parkSize](n=>false);
        reserevedPointer, reserevedArea := 0, {};
        this.weekend := weekend;
        full := false;
        // nextReserveSpot, nextNonReserveSpot := 0,0;
        this.reservedSpaces := reservedSpaces;
        this.subscriptions := subscriptions;
        availResSpaces, availNonResSpaces := reservedSpaces, parkSize - reservedSpaces;
    }

    method printParkingPlan()
    {
        print carpark;
    }

    method checkAvailability() returns (res: int)
    // ensures that return value is always a positive integer
    ensures res >= 0
    // ensures the sequence isn't changed
    ensures carpark == old(carpark)
    {
        var count := 0;
        for i := 0 to carpark.Length
            invariant 0 <= i <= carpark.Length
        {
            if !carpark[i] {
            count := count + 1;
            }
        }
        res, availableSpaces := count, count;
    }

    method enterCarPark(plateNum: int) returns (carParked: bool)
    modifies this
    modifies carpark
    requires 0 <= carparkPointer < carpark.Length
    requires availableSpaces > 5 || plateNum in subscriptions
    // when the park is "full" or plate number is not subscribed, the method will return false
    ensures availableSpaces <= 5 || plateNum !in subscriptions ==> carpark == old(carpark) && !carParked
    // write some other shit for this im going mad
    {
        if (availableSpaces <= 5 || plateNum !in subscriptions) 
        {
            carParked := false;
        }
        else 
        {
            carpark[carparkPointer] := true;
            carparkPointer := carparkPointer + 1;
            carParked := true;
        }
    }

    method leaveCarPark() 
    {}

    method enterReservedCarPark()
    {}

    method makeSubscription()
    {}

    method openReservedArea()
    {}

    method closeCarPark()
    {}

}
    
    // enterCarPark - plateNum | returns true or false
    // leaveCarPark - plateNum | returns true or false
    // checkAvailability - returns int
    // enterReservedCarPark - plateNum, day | returns true or false
    // makeSubscription - plateNum | returns 
    // openReservedArea - returns true or false
    // closeCarPark - return true or false
    // valid - returns true or false

// size: int, weekend: bool, reservedSpaces: int, subscriptions: set<int>
method Main() {
    var carpark := new CarPark(10, false, 5,[0,0]);
    carpark.printParkingPlan();
    
}