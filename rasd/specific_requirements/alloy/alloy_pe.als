open util/boolean

sig User {
	email: one String,
	name: one String,
	surname: one String,
	idCardNumber: one String,
	taxCode: one String,
	licenseIdNumber: one String,
	address: one String,
	phoneNumber: one Int,
	paymentMethod: one PaymentMethod,
	isAccountLocked: one Bool,
	userPosition: lone Position,
}

sig PaymentMethod {}

sig Car {
	carCode: one Int,
	status: one CarStatus,
	batteryLevel: one Int,
	isLocked: Bool,
	isEngineOn: Bool,
	isOnCharge: Bool,
} {
	batteryLevel >= 0 and batteryLevel <= 100
	carCode > 0
}

abstract sig CarStatus {}
one sig AVAILABLE extends CarStatus {}
one sig OUTOFSERVICE extends CarStatus {}
one sig RESERVED extends CarStatus {}
one sig INUSE extends CarStatus {}

sig Reservation {
	reservedCar: one Car,
	reservedUser: one User,
	reservationTime: one Int,
	expirationTime: one Int,
	unlockTime: lone Int,
	isActive: Bool,
	isExpired: Bool,
} {
	reservationTime < expirationTime
	unlockTime < expirationTime
	unlockTime > reservationTime
}

sig Ride {
	reservation: one Reservation,
	startTime: one Int,
	endTime: lone Int,
	originLocation: one Position,
	finalLocation: lone Position,
	driver: one User,
} {
	startTime < endTime
}

sig Float {}

sig Position {
	latitude: one Float,
	longitude: one Float,
}

//The Safe Area is unique
one sig SafeArea {
	coverage: set Position,
} {
	#coverage>0
}

fact UniqueUser {
	no u1, u2: User | (u1 != u2 and
		(u1.email = u2.email or u1.idCardNumber = u2.idCardNumber or
		u1.taxCode = u2.taxCode or u1.licenseIdNumber = u2.licenseIdNumber))
}

//no two cars reserved by the same user
fact UniqueReservation {
	no res1, res2: Reservation | (res1 != res2 and
		(res1.reservedUser = res2.reservedUser and res1.isActive = True
		and res2.isActive = True))
}

//no users con account bloccato hanno active reservations
fact NoBlockedUserReservation {
	no res: Reservation | (res.reservedUser.isAccountLocked = True)
}

fact UniqueCarCode {
	no c1, c2: Car | (c1 != c2 and c1.carCode = c2.carCode)
}

fact AvailableForRentCar {
	all c: Car | (c.status = AVAILABLE
		implies (c.batteryLevel > 20 and c. isLocked = True and c.isEngineOn = False
			and no r: Reservation | (r.reservedCar = c)))
}

fact ReservedCar {
	all c: Car | (c.status = RESERVED
		implies ((one res: Reservation | res.reservedCar = c) and 
			c.batteryLevel > 20 and c. isLocked = True and c.isEngineOn = False))
}

pred show() {}

run show for 5
