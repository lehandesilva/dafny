class {:autocontracts} CarPark {

    var parkSize: int
    var reservedSpaces: int
    var carpark: set<int> // set contains all cars including reserved cars
    var reservedArea: set<int> // set contains only reserved cars
    var subscriptions: set<int> // set contains subscribed cars
    var reservedAreaOpen: bool
    var minSpacesLeft: int // always 5

        //arguments - reserved area space, day, normal spaces, array of exisiting subscribed cars, closing time 
    constructor(parkSize: int, reservedSpaces: int, subscriptions: set<int>) 
        requires parkSize > 6 //size should always be a positive number
        requires parkSize > reservedSpaces && reservedSpaces > 0 //total spots alaways greater than 0 and the reserved spaces
        requires |subscriptions| <= reservedSpaces // subscriptions cant be greater than the reserved spaces
    {
        this.parkSize := parkSize;
        carpark := {};
        reservedArea :=  {};
        minSpacesLeft := 5;
        this.reservedSpaces := reservedSpaces;
        this.subscriptions := subscriptions;
    }

    ghost predicate Valid() {
        //number of subscriptions must not be greater than reserved spaces
        reservedSpaces >= |subscriptions|
    }

    ghost predicate canEnter() {
        // if the reserved area is open, the available spaces wont count the reserved spaces
        // and would imply that they available for everyone as well
        (reservedAreaOpen && (parkSize - minSpacesLeft - |carpark| > 0)) || 
        (!reservedAreaOpen && (parkSize - minSpacesLeft - |carpark| - reservedSpaces > 0))
    }

    method enterCarPark(plateNum: int) returns (carParked: bool)
    // checks canEnter predicate to check available spaces and if the car can enter
    ensures  canEnter() ==> carParked
    // If reserved area is not open but the carpark is full, allow reserved cars in
    ensures !reservedAreaOpen && plateNum in subscriptions ==> carParked 
    // If true, the car will be added to the set containing all cars
    ensures carParked ==> (carpark == old(carpark) + {plateNum})
    {
        if ((reservedAreaOpen && (parkSize - minSpacesLeft - |carpark| > 0)) || (!reservedAreaOpen && (parkSize - minSpacesLeft - |carpark| - reservedSpaces > 0)) || plateNum in subscriptions){
            carpark := carpark + {plateNum};
            carParked := true;
        }
        else {
            carParked := false;
        }
    }

    method leaveCarPark(plateNum: int)
    // the car should already be in the set before removing it
    requires plateNum in carpark
    // the car will be removed from the carpark (applies for both reserved and non-reserved cars)
    ensures carpark == old(carpark) - {plateNum}
    // if the car is in the reserved area, it will be removed 
    ensures reservedArea == old(reservedArea) - {plateNum}
    {
        // removes the car from the carpark
        carpark := carpark - {plateNum};
        // removes the car from reserved area if it is in it
        if (plateNum in reservedArea) {
            reservedArea := reservedArea - {plateNum};
        }
    }

    method checkAvailability() returns (availableSpaces: int)
    /* 
    if the reserved area is open, the available spaces would return the remainder after subtracting 
    the 5 spaces left for the inconsiderate drivers and the already occupied spaces
    */
    ensures reservedAreaOpen ==> parkSize - minSpacesLeft - |carpark| == availableSpaces
    // if the reserved area is NOT open, the 
    ensures !reservedAreaOpen ==> parkSize - minSpacesLeft - reservedSpaces - (|carpark|  - |reservedArea|) == availableSpaces
    // the carpark will not changed when called
    ensures old(carpark) == carpark
    {
        if (reservedAreaOpen) {
            availableSpaces := parkSize - minSpacesLeft - |carpark|;
        }
        else {
            availableSpaces := parkSize - minSpacesLeft - reservedSpaces - (|carpark| - |reservedArea|);
        }
    }

    method enterReservedCarPark(plateNum: int) returns (carParked: bool)
    // car can enter if the reserved area is open or if it is subscribed
    requires plateNum in subscriptions || reservedAreaOpen
    // if the reserved area is closed, the subscribed car will be added and reserved area set will change
    ensures !reservedAreaOpen ==> reservedArea == old(reservedArea) + {plateNum}
    {
        if (!reservedAreaOpen){
            reservedArea := reservedArea + {plateNum};
        }
        carParked := true;
    }

    method makeSubscription(plateNum: int) returns (subscribed: bool)
    // the plate number will be added to the set containing all subscriptions
    ensures |subscriptions| < reservedSpaces ==> subscriptions == (old(subscriptions) + {plateNum})
    {
        if (|subscriptions| < reservedSpaces) {
            subscriptions := subscriptions + {plateNum};
            subscribed := true;
        }
        else {
            subscribed := false;
        }
    }

    method openReservedArea()
    // the second barrier will be opened so the reservedAreaOpen set to true
    ensures reservedAreaOpen
    {
        reservedAreaOpen := true;
    }

    method closeCarPark()
    // the sets will be emptied and the reserved area will be set to false to close the second barrier
    ensures reservedArea == {} && carpark == {} && !reservedAreaOpen
    {
        reservedArea := {};
        carpark := {};
        reservedAreaOpen := false;
    }

    method printParkingPlan()
    {
        print "\nWhole car park : \n";
        print |carpark|;
        print carpark;
        print "\nReserved Area : \n";
        print |reservedArea|;
        print reservedArea;

    }
}

// (parkSize: int, reservedSpaces: int, subscriptions: set<int>) 
method Main() {
    print "Test case: 1";
    // Test case 1:
    // creating a car park with 15 spaces with 5 reserved spaces. This would mean only 5 
    // spaces non reserved spaces woulf be left. Adding anything more would return false 
    // unless it is subscribed
    var carpark := new CarPark(15, 5, {});
    var car1 := carpark.enterCarPark(1);
    var car2 := carpark.enterCarPark(2);
    var car3 := carpark.enterCarPark(3);
    var car4 := carpark.enterCarPark(4);
    var car5 := carpark.enterCarPark(5);
    // car 6 can enter even though the carpark is full as it is subscribed
    var subscribed := carpark.makeSubscription(6);
    carpark.printParkingPlan();
    var car6 := carpark.enterCarPark(6);
    if (6 in carpark.subscriptions) {
        var enteredreserved := carpark.enterReservedCarPark(6);
    }
    // cars attempting to enter after would return false as they aren't subscribed
    var car7 := carpark.enterCarPark(7);
    if (5 in carpark.carpark){
        carpark.leaveCarPark(5);
    }
    var car8 := carpark.enterCarPark(8);
    carpark.printParkingPlan();
    // carpark would be emptied
    carpark.closeCarPark();
    carpark.printParkingPlan();
    print "\nTest Case: 2";
    // Trying to enter 6 non subscribed cars when only 5 allowed and once reserved area is open
    // testing if cars can enter reserved area even if they aren't subscribed
    var carpark2 := new CarPark(15, 5, {});
    var car9 := carpark2.enterCarPark(9);
    var car10 := carpark2.enterCarPark(10);
    var car11 := carpark2.enterCarPark(11);
    var car12 := carpark2.enterCarPark(12);
    var car13 := carpark2.enterCarPark(13);
    var car14 := carpark2.enterCarPark(14);
    carpark2.printParkingPlan();
    carpark2.openReservedArea();
    var car15 := carpark2.enterCarPark(15);
    if (carpark2.reservedAreaOpen){
        var enteredreserved2 := carpark2.enterReservedCarPark(15);
    }
    var car16 := carpark2.enterCarPark(16);
    if (carpark2.reservedAreaOpen){
        var enteredreserved3 := carpark2.enterReservedCarPark(16);
    }
    carpark2.printParkingPlan();
}