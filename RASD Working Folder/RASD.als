abstract sig Bool{}
one sig True extends Bool{}
one sig False extends Bool{}

sig FiscalCode{}

sig ThirdPartyId{}

sig Username{}

sig Password{}

sig Registration{
    username: one Username,
    password: one Password
}

abstract sig Customer{
    registration: one Registration,
    accessRights: one String
}

sig User extends Customer{
    fiscalCode: one FiscalCode,
}

sig ThirdParty extends Customer{
    id: one ThirdPartyId
}
--------Do we really need them?
sig PoliceOfficer extends ThirdParty{}

sig MunicipalEmployee extends ThirdParty{}
--------------------------------------
sig Location{
    latitude: one Int,
    longitude: one Int
}
{latitude >= -90 and latitude <= 90 and longitude >= -180 and longitude <= 180}

sig HardEvidence{}

sig LicensePlate{}

sig TimeStamp{}

sig Violation{
    id: one Int,
    licensePlate: one LicensePlate,
    location: one Location,
    spotter: one User,
    timestamp: one TimeStamp,
    hardEvidence: some HardEvidence,
    isValid: one Bool
}

sig Ticket{
    amount: one Int,
    id: one String,
    violation: one Violation
}

--All FiscalCodes must be associated to a User
fact FiscalCodeMustBeAssociatedToUser{
    all f : FiscalCode | some u : User | f in u.fiscalCode
}

--A Fiscal Code or Third Party Id can be associated to only one user
fact OneUserFiscalCode{
    no disj u1,u2 : User | u1.fiscalCode = u2.fiscalCode
} 

--Only one id per violation, no replicas!
fact OneThirdPartyUserId{
    no disj t1, t2 : ThirdParty | t1.id = t2.id
}

--Only one id per violation, no replicas!
fact OneIDViolation{
    no disj v1, v2 : Violation | v1.id = v2.id
}

--It is not possible to have two different locations with the same plate and timestamp
fact SamePlateLocationAndTimestamp {
    all v1, v2 : Violation | 
    v1.location = v2.location implies (v1.licensePlate = v2.licensePlate and v1.timestamp = v2.timestamp)
}

