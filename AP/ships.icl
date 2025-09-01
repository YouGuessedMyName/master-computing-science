module ships
import StdEnv
from Math.Geometry import pi

r_earth :== 6371.009  // radius of Earth in km

:: Ship
 =	{ name      :: !String
	, size      :: !Int
	, kind      :: !Kind
	, flag      :: !Country
	, status    :: !Status
	, position  :: !Position
	}
:: Position
 =	{ latitude  :: !Real
	, longitude :: !Real
	}
:: Farm
 =	{ name      :: !String
	, country   :: !Country
	, position  :: !Position
	}
:: Port
 =	{ name      :: !String
	, position  :: !Position
	}
:: Kind    = Cargo | Fisher | Navy | Tanker | Tugboat
:: Country = NL | UK | DE | FR | BE | BR | VE | PH | DK | LR | MT
:: Status  = Underway | Moored

distance :: a b -> Real | toPosition a & toPosition b
distance a b = r_earth * sqrt (dLat ^ 2.0 + (cos mLat * dLong) ^ 2.0)
where
	p     = toPosition a
	q     = toPosition b
	dLat  = (p.latitude  - q.latitude)  * pi / 180.0
	mLat  = (p.latitude  + q.latitude)  * pi / 360.0
	dLong = (p.longitude - q.longitude) * pi / 180.0
	mLong = (p.longitude + q.longitude) * pi / 360.0

class toPosition a :: a -> Position
instance toPosition Position where toPosition p = p
instance toPosition Ship     where toPosition s = s.Ship.position
instance toPosition Farm     where toPosition w = w.Farm.position
instance toPosition Port     where toPosition p = p.Port.position

ports :: [Port]
ports
 = [ { Port 
     | name     = "Texel"
	 , position = {latitude = 53.03933, longitude = 4.85035}
	 }
   , { Port 
     | name     = "Den Helder"
	 , position = {latitude = 52.95938, longitude = 4.79614}
	 }
   ]

ships :: [Ship]
ships
 = [ { name     = "TX10 Emmie"
	 , size     = 41
	 , kind     = Fisher
	 , flag     = NL
	 , status   = Moored
	 , position = {latitude = 53.03957, longitude = 4.85033}
	 }
   , { name     = "TX27 NOVA CURA"
	 , size     = 23
	 , kind     = Fisher
	 , flag     = NL
	 , status   = Underway
	 , position = {latitude = 53.04125, longitude = 4.85224}
	 }
   , { name     = "HNLMS Tromp"
	 , size     = 144
	 , kind     = Navy
	 , flag     = NL
	 , status   = Moored
	 , position = {latitude = 52.95939, longitude = 4.79615}
	 }
   , { name     = "NATO WARSHIP M111"
	 , size     = 53
	 , kind     = Navy
	 , flag     = UK
	 , status   = Underway
	 , position = {latitude = 52.98099, longitude = 4.76725}
	 }
   , { name     = "HNLMS Schiedam"
	 , size     = 52
	 , kind     = Navy
	 , flag     = NL
	 , status   = Underway
	 , position = {latitude = 52.98308, longitude = 4.57119}
	 }
   , { name     = "MSC Bari"
	 , size     = 366
	 , kind     = Cargo
	 , flag     = LR
	 , status   = Underway
	 , position = {latitude = 52.04863, longitude = 3.56977}
	 }
   , { name     = "Sea empress"
	 , size     = 182
	 , kind     = Tanker
	 , flag     = MT
	 , status   = Underway
	 , position = {latitude = 51.90038, longitude = 3.5334}
	 }
   ]

farms :: [Farm]
farms
 = [ { name     = "Egmond aan Zee"
	 , country  = NL
	 , position = {latitude = 52.606, longitude = 4.419}
	 }
   , { name     = "Prinses Amalia"
	 , country  = NL
	 , position = {latitude = 52.589444, longitude = 4.206281}
	 }
   , { name     = "Gemini"
	 , country  = NL
	 , position = {latitude = 54.036111, longitude = 5.963056}
	 }
   , { name     = "Dudgeon"
	 , country  = UK
	 , position = {latitude = 53.25, longitude = 1.383333}
	 }
   , { name     = "Horns Rev II"
	 , country  = DK
	 , position = {latitude = 55.6, longitude = 7.59}
	 }
   ]
