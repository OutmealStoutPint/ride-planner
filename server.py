"""Ride Planner — first functional local web app (zero external dependencies).

Run:  python server.py    then open http://localhost:8000 in your browser.

Path A: this Python process is the "engine" (route generation + scoring + live
weather), the browser shows the page and a real map. Uses only the Python standard
library, so there is nothing to pip-install.
"""
import copy, json, math, os, time, urllib.parse, urllib.request
from concurrent.futures import ThreadPoolExecutor
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer

HERE = os.path.dirname(os.path.abspath(__file__))
UA = {"User-Agent": "RidePlannerLocal/0.1 (personal gravel ride planner)"}
EV_RANGE_KM = 380           # 2021 Kia Soul EV
PORT = int(os.environ.get("PORT", 8000))   # hosting platforms set $PORT

# tiny in-memory result cache: same request within TTL skips the slow live calls
# (also eases public-API rate limits, e.g. Overpass). Weather changes slowly, so a
# short TTL is fine.
_CACHE = {}
_CACHE_TTL = 1800           # seconds (30 min)
def _cache_get(key):
    v = _CACHE.get(key)
    return v[1] if v and time.time()-v[0] < _CACHE_TTL else None
def _cache_put(key, val):
    _CACHE[key] = (time.time(), val)

BUSY   = {"primary","secondary","trunk","primary_link","secondary_link","trunk_link"}
GRAVEL = {"fine_gravel","gravel","unpaved","compacted","ground","dirt","earth","sand","pebblestone"}
TRAIL  = {"cycleway","path","track","bridleway"}
COMPASS = ["N","NE","E","SE","S","SW","W","NW"]

def getj(url):
    with urllib.request.urlopen(urllib.request.Request(url, headers=UA), timeout=45) as r:
        return json.load(r)

def compass(b): return COMPASS[round(b/45) % 8]

def haversine(a, b):
    R=6371000; lo1,la1=a; lo2,la2=b
    p1,p2=math.radians(la1),math.radians(la2)
    h=math.sin(math.radians(la2-la1)/2)**2+math.cos(p1)*math.cos(p2)*math.sin(math.radians(lo2-lo1)/2)**2
    return 2*R*math.asin(math.sqrt(h))

def bearing(a, b):
    lo1,la1=map(math.radians,a); lo2,la2=map(math.radians,b); dl=lo2-lo1
    x=math.sin(dl)*math.cos(la2); y=math.cos(la1)*math.sin(la2)-math.sin(la1)*math.cos(la2)*math.cos(dl)
    return (math.degrees(math.atan2(x,y))+360)%360

def angdiff(a,b):
    d=abs(a-b)%360; return min(d,360-d)

def deloop(coords, tol_m=45, max_frac=0.30):
    # loop-erased walk: whenever the route returns within tol_m of an earlier point,
    # erase the excursion in between (a spur / out-and-back / waypoint bulge). The
    # max_frac guard protects the main loop's return-to-start from being erased.
    if len(coords)<4: return coords
    total=sum(haversine(coords[i-1][:2],coords[i][:2]) for i in range(1,len(coords)))
    out=[]
    for p in coords:
        hit=None
        for k in range(len(out)-3):
            if haversine(out[k][:2], p[:2])<tol_m: hit=k; break
        if hit is not None:
            exc=out[hit:]+[p]
            exclen=sum(haversine(exc[j-1][:2],exc[j][:2]) for j in range(1,len(exc)))
            if exclen < max_frac*total: del out[hit+1:]
        out.append(p)
    return out

def geocode(q):
    url="https://nominatim.openstreetmap.org/search?"+urllib.parse.urlencode(
        {"q":q,"format":"json","limit":1,"countrycodes":"ca"})
    res=getj(url)
    if not res: raise ValueError(f"Could not find location: {q}")
    return float(res[0]["lon"]), float(res[0]["lat"]), res[0]["display_name"].split(",")[0]

def brouter(via):
    ll="|".join(f"{lo},{la}" for lo,la in via)
    url="https://brouter.de/brouter?"+urllib.parse.urlencode(
        {"lonlats":ll,"profile":"trekking","alternativeidx":0,"format":"geojson"})
    for attempt in range(2):
        try: return getj(url)
        except urllib.error.HTTPError as e:
            if e.code==429 and attempt==0: time.sleep(4)
            else: raise

def overpass(q):
    data=urllib.parse.urlencode({"data":q}).encode()
    req=urllib.request.Request("https://overpass-api.de/api/interpreter", data=data, headers=UA)
    with urllib.request.urlopen(req, timeout=55) as r: return json.load(r)

def pt_seg_dist(px,py,ax,ay,bx,by):
    dx,dy=bx-ax,by-ay
    if dx==0 and dy==0: return math.hypot(px-ax,py-ay)
    t=max(0.0,min(1.0,((px-ax)*dx+(py-ay)*dy)/(dx*dx+dy*dy)))
    return math.hypot(px-(ax+t*dx), py-(ay+t*dy))

def analyze(gj):
    f=gj["features"][0]; p=f["properties"]; msgs=p["messages"]; hdr=msgs[0]
    wi=hdr.index("WayTags"); di=hdr.index("Distance")
    tot=gravel=busy=0
    for row in msgs[1:]:
        d=int(row[di]); tot+=d
        tags=dict(t.split("=",1) for t in row[wi].split() if "=" in t)
        hw=tags.get("highway",""); sf=tags.get("surface","")
        if hw in BUSY: busy+=d
        if sf in GRAVEL or hw in TRAIL: gravel+=d
    coords=f["geometry"]["coordinates"]; acc=0; head=coords[-1][:2]
    for i in range(1,len(coords)):
        acc+=haversine(coords[i-1][:2],coords[i][:2])
        if acc>=2000: head=coords[i][:2]; break
    # retrace detection: distance covered on a segment ridden in both directions
    # (an out-and-back "dead end"). Used to penalise spurs in scoring.
    seglen={}
    for i in range(1,len(coords)):
        a=coords[i-1]; b=coords[i]
        key=tuple(sorted(((round(a[0],5),round(a[1],5)),(round(b[0],5),round(b[1],5)))))
        seglen.setdefault(key,[0,0]); seglen[key][0]+=1
        seglen[key][1]+=haversine(a[:2],b[:2])
    retrace=sum(L for c,L in seglen.values() if c>=2)
    # U-turn count: resample to ~250 m and count near-reversals (the tip of any
    # dead-end / out-and-back lobe). Catches spurs that exact-retrace misses.
    res=[coords[0]]; a2=0
    for i in range(1,len(coords)):
        a2+=haversine(coords[i-1][:2],coords[i][:2])
        if a2>=250: res.append(coords[i]); a2=0
    uturn=0
    for i in range(1,len(res)-1):
        if angdiff(bearing(res[i-1][:2],res[i][:2]), bearing(res[i][:2],res[i+1][:2]))>150:
            uturn+=1
    return dict(km=tot/1000, gravel=100*gravel/tot, busy=100*busy/tot,
                retrace=100*retrace/tot, uturn=uturn,
                bearing=bearing(coords[0][:2],head), coords=[[c[0],c[1]] for c in coords])

def weather(lon, lat):
    w=getj("https://api.open-meteo.com/v1/forecast?"+urllib.parse.urlencode({
        "latitude":lat,"longitude":lon,"timezone":"America/Toronto","wind_speed_unit":"kmh",
        "forecast_days":4,
        "hourly":"temperature_2m,wind_speed_10m,wind_direction_10m,precipitation_probability"}))
    h=w["hourly"]; days={}
    for i,t in enumerate(h["time"]):
        hr=int(t[11:13])
        if 8<=hr<=16: days.setdefault(t[:10],[]).append(i)
    best=None
    for day,idx in sorted(days.items()):
        if len(idx)<4: continue
        rain=max(h["precipitation_probability"][i] for i in idx)
        wind=sum(h["wind_speed_10m"][i] for i in idx)/len(idx)
        temp=max(h["temperature_2m"][i] for i in idx)
        s=sum(math.sin(math.radians(h["wind_direction_10m"][i])) for i in idx)
        c=sum(math.cos(math.radians(h["wind_direction_10m"][i])) for i in idx)
        wfrom=(math.degrees(math.atan2(s,c))+360)%360
        cand=dict(day=day,rain=rain,wind=round(wind),temp=round(temp),wind_from=wfrom)
        # pick the best ride day this week: least rain, then lightest wind
        key=(rain,wind)
        if best is None or key<best["_key"]: cand["_key"]=key; best=cand
    aqhi=None
    try:
        a=getj("https://api.weather.gc.ca/collections/aqhi-forecasts-realtime/items?"+urllib.parse.urlencode(
            {"bbox":f"{lon-0.8},{lat-0.6},{lon+0.8},{lat+0.6}","limit":1,"sortby":"-forecast_datetime","f":"json"}))
        if a["features"]: aqhi=a["features"][0]["properties"]["aqhi"]
    except Exception: pass
    notes=[]; verdict="Good to go"; level="good"
    if best["rain"]>=60: verdict="Not recommended"; level="bad"; notes.append(f"Rain likely most of the day ({best['rain']}%).")
    elif best["rain"]>=40: verdict="Caution"; level="warn"; notes.append(f"Some rain risk ({best['rain']}%).")
    if best["wind"]>=28:
        if level=="good": verdict="Caution"; level="warn"
        notes.append(f"Breezy ({best['wind']} km/h) — ride {compass(best['wind_from'])} first for a tailwind home.")
    else:
        notes.append(f"Start heading {compass(best['wind_from'])} (into the wind) for a tailwind on the way back.")
    if best["temp"]>=28: notes.append(f"Hot ({best['temp']}°C) — start early to beat the heat.")
    if aqhi and aqhi>=7: verdict="Not recommended"; level="bad"; notes.append(f"Poor air quality (AQHI {aqhi}).")
    best.update(verdict=verdict,level=level,notes=notes,aqhi=aqhi); best.pop("_key",None)

    # build the full 4-day summary for display
    forecast=[]
    for day,idx in sorted(days.items()):
        if len(idx)<1: continue
        rain=max(h["precipitation_probability"][i] for i in idx)
        wind=sum(h["wind_speed_10m"][i] for i in idx)/len(idx)
        temp=max(h["temperature_2m"][i] for i in idx)
        day_verdict="Good to go"
        if rain>=60: day_verdict="Rain likely"
        elif rain>=40: day_verdict="Some rain risk"
        if round(wind)>=28:
            day_verdict="Breezy" if day_verdict=="Good to go" else day_verdict+", breezy"
        forecast.append({"day":day,"rain":rain,"wind":round(wind),"temp":round(temp),"verdict":day_verdict,"best":day==best["day"]})
    best["forecast"]=forecast
    return best

def gen_loop(center, base, R, n=6):
    # n waypoints evenly around a ring -> a rounder polygon loop = fewer out-and-back
    # spurs than a sparse 3-point triangle. First waypoint sits at `base` so the
    # outbound leg can be aimed into the wind.
    KM_LAT=111.13; KM_LON=111.32*math.cos(math.radians(center[1]))
    def wp(b): return (center[0]+(R/KM_LON)*math.sin(math.radians(b)),
                       center[1]+(R/KM_LAT)*math.cos(math.radians(b)))
    return [center]+[wp(base+k*360/n) for k in range(n)]+[center]

def score(a, target, wind_from, surface):
    dist_pen=abs(a["km"]-target)/target*100
    wind=100-(angdiff(a["bearing"],wind_from)/180*100)
    gw={"trail":2.0,"mix":1.0,"road":-0.6}[surface]
    return a["gravel"]*gw - a["busy"]*3.0 - dist_pen*0.9 + wind*0.5 - a["retrace"]*2.5 - a["uturn"]*5

def generate_outback(center, target, wind_from):
    half=target/2
    KM_LAT=111.13; KM_LON=111.32*math.cos(math.radians(center[1]))
    def endpoint(bear,dist):
        return (center[0]+(dist/KM_LON)*math.sin(math.radians(bear)),
                center[1]+(dist/KM_LAT)*math.cos(math.radians(bear)))
    jobs=[(wind_from,half),(wind_from+45,half),(wind_from-45,half)]
    def work(job):
        bear,dist=job
        gj=brouter([center,endpoint(bear,dist)])
        a=analyze(gj)
        dist_pen=abs(a["km"]*2-target)/target*100
        wind=100-(angdiff(a["bearing"],wind_from)/180*100)
        a["score"]=a["gravel"]*2.0 - a["busy"]*3.0 - dist_pen*0.9 + wind*0.5
        a["km"]=round(a["km"]*2,1)
        a["coords"]=a["coords"]+list(reversed(a["coords"][:-1]))
        return a
    cands=[]
    with ThreadPoolExecutor(max_workers=3) as ex:
        for f in [ex.submit(work,j) for j in jobs]:
            try: cands.append(f.result())
            except Exception: pass
    if not cands: raise RuntimeError("Could not build a route here — try a different start or distance.")
    return max(cands, key=lambda x:x["score"])

def _fetch_candidates(center, target, wind_from):
    base_R=max(1.5, target/11.5)
    jobs=[(wind_from,base_R),(wind_from,base_R*1.2),
          (wind_from+60,base_R),(wind_from-60,base_R)]
    def work(job, delay=0):
        if delay: time.sleep(delay)
        base,R=job
        return analyze(brouter(gen_loop(center,base,R)))
    cands=[]
    with ThreadPoolExecutor(max_workers=4) as ex:
        futures=[ex.submit(work,j,i*1.0) for i,j in enumerate(jobs)]
        for f in futures:
            try: cands.append(f.result())
            except Exception: pass
    if not cands: raise RuntimeError("Could not build a route here — try a different start or distance.")
    return cands

def _finalize(cand):
    c=copy.deepcopy(cand)
    c["coords"]=deloop(c["coords"])
    cc=c["coords"]
    c["km"]=sum(haversine(cc[i-1],cc[i]) for i in range(1,len(cc)))/1000
    return c

def generate(center, target, wind_from, surface):
    cands=_fetch_candidates(center, target, wind_from)
    for a in cands: a["score"]=score(a,target,wind_from,surface)
    return _finalize(max(cands, key=lambda x:x["score"]))

def generate_both(center, target, wind_from, surface):
    cands=_fetch_candidates(center, target, wind_from)
    # Route A: wind-smart (full score including wind alignment term)
    for a in cands: a["wind_score"]=score(a,target,wind_from,surface)
    wi=max(range(len(cands)), key=lambda i:cands[i]["wind_score"])
    # Route B: best gravel (same score but wind term removed)
    gw={"trail":2.0,"mix":1.0,"road":-0.6}.get(surface,1.0)
    for a in cands:
        dist_pen=abs(a["km"]-target)/target*100
        a["gravel_score"]=a["gravel"]*gw - a["busy"]*3.0 - dist_pen*0.9 - a["retrace"]*2.5 - a["uturn"]*5
    gi=max(range(len(cands)), key=lambda i:cands[i]["gravel_score"])
    route_a=_finalize(cands[wi])
    same=(wi==gi)
    route_b=None if same else _finalize(cands[gi])
    return route_a, route_b, same

def decorate(coords):
    # walk the full route; drop a km marker every 5 km and a direction arrow every
    # 2.5 km, interpolated onto the line. coords are [lon,lat].
    markers=[]; arrows=[]; acc=0.0; next_km=5000; next_arrow=1500; ARROW=2500
    for i in range(1,len(coords)):
        a=coords[i-1]; b=coords[i]; seg=haversine(a[:2],b[:2])
        brg=round(bearing(a[:2],b[:2]))
        while seg>0 and acc+seg>=next_arrow:
            t=(next_arrow-acc)/seg
            arrows.append([round(a[1]+(b[1]-a[1])*t,6), round(a[0]+(b[0]-a[0])*t,6), brg])
            next_arrow+=ARROW
        while seg>0 and acc+seg>=next_km:
            t=(next_km-acc)/seg
            markers.append([round(a[1]+(b[1]-a[1])*t,6), round(a[0]+(b[0]-a[0])*t,6), next_km//1000])
            next_km+=5000
        acc+=seg
    return markers, arrows

def maneuvers(coords, look_m=25, turn_deg=35, merge_m=40):
    # Turn-by-turn maneuvers from geometry (BRouter's public geojson omits voicehints).
    # At each point compare the heading ~look_m before vs after; a large, localised
    # heading change is a turn (gentle curves spread over many points stay below the
    # threshold). coords are [lon,lat].
    n=len(coords)
    if n<3: return []
    cum=[0.0]*n
    for i in range(1,n): cum[i]=cum[i-1]+haversine(coords[i-1][:2],coords[i][:2])
    raw=[]
    for i in range(1,n-1):
        j=i
        while j>0 and cum[i]-cum[j]<look_m: j-=1
        k=i
        while k<n-1 and cum[k]-cum[i]<look_m: k+=1
        if j==i or k==i: continue
        turn=((bearing(coords[i][:2],coords[k][:2])-bearing(coords[j][:2],coords[i][:2]))+540)%360-180
        if abs(turn)>=turn_deg: raw.append((i,cum[i],turn))
    merged=[]                                   # merge near-duplicate points, keep sharpest
    for m in raw:
        if merged and m[1]-merged[-1][1]<merge_m:
            if abs(m[2])>abs(merged[-1][2]): merged[-1]=m
            continue
        merged.append(m)
    def classify(t):
        side="right" if t>0 else "left"; a=abs(t)
        if a>=160: return "u-turn","Make a U-turn"
        if a>=110: return "sharp_"+side,"Sharp "+side
        if a>=70:  return side,"Turn "+side
        return "slight_"+side,"Slight "+side
    res=[]
    for i,dist,turn in merged:
        typ,instr=classify(turn)
        oc=coords[-1]; a2=0.0                 # sample ~15 m past the turn = road turned ONTO
        for k in range(i,len(coords)-1):
            a2+=haversine(coords[k][:2],coords[k+1][:2])
            if a2>=15: oc=coords[k+1]; break
        res.append({"lat":round(coords[i][1],6),"lon":round(coords[i][0],6),
                    "type":typ,"instruction":instr,"angle":round(turn),
                    "street":None,"dist_from_start_m":round(dist),
                    "_onto":[oc[0],oc[1]]})
    return res

def add_street_names(coords, turns):
    # One Overpass query for all named roads in the route bbox, then match each
    # maneuver's "onto" point to the nearest named way locally (fast, 1 network call).
    if not turns: return
    lats=[c[1] for c in coords]; lons=[c[0] for c in coords]; pad=0.005
    q=(f'[out:json][timeout:40];way["highway"]["name"]'
       f'({min(lats)-pad},{min(lons)-pad},{max(lats)+pad},{max(lons)+pad});out geom;')
    try: data=overpass(q)
    except Exception: return
    lat0=math.radians(sum(lats)/len(lats)); cosl=math.cos(lat0)
    xy=lambda lat,lon:(lon*cosl*111320.0, lat*110540.0)
    P=[]
    for el in data.get("elements",[]):
        name=el.get("tags",{}).get("name"); g=el.get("geometry") or []
        for a,b in zip(g,g[1:]):
            P.append((xy(a["lat"],a["lon"]), xy(b["lat"],b["lon"]), name))
    if not P: return
    for m in turns:
        op=m.get("_onto",[m["lon"],m["lat"]]); px,py=xy(op[1],op[0])
        best=None; bestd=1e18
        for (ax,ay),(bx,by),name in P:
            d=pt_seg_dist(px,py,ax,ay,bx,by)
            if d<bestd: bestd=d; best=name
        if best and bestd<40:
            m["street"]=best; m["instruction"]=m["instruction"]+" onto "+best

def _route_payload(r, surface, label, description):
    coords2=r["coords"][::4]+[r["coords"][-1]]
    mkr,arr=decorate(r["coords"])
    return {"latlngs":[[c[1],c[0]] for c in coords2],"markers":mkr,"arrows":arr,
            "km":round(r["km"],1),"gravel":round(r["gravel"]),"busy":round(r["busy"]),
            "heading":compass(r["bearing"]),"type":surface,"label":label,"description":description}

def plan(home_q, start_q, target, surface, ev_range_km=None):
    h_lon,h_lat,h_name=geocode(home_q)
    s_lon,s_lat,s_name=geocode(start_q)
    wx=weather(s_lon,s_lat)
    wind_dir=compass(wx["wind_from"])
    if surface=="outback":
        route=generate_outback((s_lon,s_lat), target, wx["wind_from"])
        route_a=_route_payload(route,surface,"Out-and-back",
            f"Heads {wind_dir} into the wind — tailwind home · {round(route['gravel'])}% gravel · {round(route['busy'])}% busy road")
        turns=maneuvers(route["coords"]); add_street_names(route["coords"],turns)
        for m in turns: m.pop("_onto",None)
        route_a["maneuvers"]=turns; route_b=None; routes_same=True
    else:
        ra,rb,routes_same=generate_both((s_lon,s_lat),target,wx["wind_from"],surface)
        turns=maneuvers(ra["coords"]); add_street_names(ra["coords"],turns)
        for m in turns: m.pop("_onto",None)
        route_a=_route_payload(ra,surface,"Wind-smart route",
            f"Heads {wind_dir} into the wind — tailwind home · {round(ra['gravel'])}% gravel · {round(ra['busy'])}% busy road")
        route_a["maneuvers"]=turns
        route_b=_route_payload(rb,surface,"Best gravel route",
            f"Maximizes trail & gravel — wind ignored · {round(rb['gravel'])}% gravel · {round(rb['busy'])}% busy road") if rb else None
    one_way=haversine((h_lon,h_lat),(s_lon,s_lat))/1000*1.3
    rt=one_way*2; range_km=ev_range_km if ev_range_km else EV_RANGE_KM; ok=rt<range_km*0.85
    return {
        "home":{"name":h_name},"start":{"name":s_name,"lat":s_lat,"lon":s_lon},
        "route":route_a,"route2":route_b,"routes_same":routes_same,
        "weather":{"day":wx["day"],"verdict":wx["verdict"],"level":wx["level"],
                   "wind":wx["wind"],"wind_from":wind_dir,
                   "temp":wx["temp"],"rain":wx["rain"],"aqhi":wx["aqhi"],
                   "notes":wx["notes"],"forecast":wx.get("forecast",[])},
        "ev":{"one_way":round(one_way),"round_trip":round(rt),"ok":ok,"range_used":round(range_km),
              "msg":("~%d km round trip — within your %d km EV range, no charging needed."%(round(rt),round(range_km))) if ok
                    else ("~%d km round trip — near/over your %d km EV range, plan a charging stop."%(round(rt),round(range_km)))},
    }

class H(BaseHTTPRequestHandler):
    def log_message(self,*a): pass
    def _send(self,code,body,ctype):
        self.send_response(code); self.send_header("Content-Type",ctype)
        self.send_header("Access-Control-Allow-Origin","*")    # let Flutter web / any client call us
        self.send_header("Content-Length",str(len(body))); self.end_headers(); self.wfile.write(body)
    def do_OPTIONS(self):                                      # CORS preflight
        self.send_response(204)
        self.send_header("Access-Control-Allow-Origin","*")
        self.send_header("Access-Control-Allow-Methods","GET, OPTIONS")
        self.send_header("Access-Control-Allow-Headers","*"); self.end_headers()
    def do_GET(self):
        u=urllib.parse.urlparse(self.path)
        if u.path=="/health":
            self._send(200,b'{"status":"ok"}',"application/json")
        elif u.path in ("/","/index.html"):
            try:
                with open(os.path.join(HERE,"index.html"),"rb") as f:
                    self._send(200,f.read(),"text/html; charset=utf-8")
            except FileNotFoundError:                          # headless backend (no test page)
                self._send(200,b'{"status":"ok","api":"/api/plan"}',"application/json")
        elif u.path=="/api/plan":
            q=urllib.parse.parse_qs(u.query)
            key=u.query
            cached=_cache_get(key)
            if cached is not None:
                self._send(200,cached,"application/json"); return
            try:
                ev_range=float(q["ev_range"][0]) if "ev_range" in q else None
                res=plan(q.get("home",["Pickering, ON"])[0], q.get("start",["Lindsay, ON"])[0],
                         float(q.get("distance",["45"])[0]), q.get("surface",["mix"])[0],
                         ev_range_km=ev_range)
                body=json.dumps(res).encode()
                mans=res["route"]["maneuvers"]      # don't cache a degraded (un-named) result:
                if not mans or any(t.get("street") for t in mans):  # only cache good responses
                    _cache_put(key,body)
                self._send(200,body,"application/json")
            except Exception as e:
                self._send(400,json.dumps({"error":str(e)}).encode(),"application/json")
        else:
            self._send(404,b"not found","text/plain")

if __name__=="__main__":
    host=os.environ.get("HOST","0.0.0.0")     # 0.0.0.0 so a hosting platform can reach it
    print(f"Ride Planner engine on http://localhost:{PORT}  (health: /health, api: /api/plan)")
    ThreadingHTTPServer((host,PORT),H).serve_forever()
