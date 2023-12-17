import os
import logging
from logging.handlers import TimedRotatingFileHandler
from flask import Flask
from flask_migrate import Migrate
from flask_sqlalchemy import SQLAlchemy
from dotenv import load_dotenv
load_dotenv()

app = Flask(__name__)

# ------------------ Logging ------------------
app.logger.setLevel(logging.INFO)
log_handler = TimedRotatingFileHandler('logs/app.log', when='midnight', interval=1, backupCount=30) # 30 days
log_handler.setLevel(logging.INFO)
formatter = logging.Formatter('%(asctime)s - %(levelname)s - %(message)s')
log_handler.setFormatter(formatter) 
app.logger.addHandler(log_handler)
# ------------------ Logging ------------------


app.secret_key = os.getenv('APP_SECKET_KEY')

# ------------------ App Config ------------------
app.config['DEBUG'] = True
app.config['SQLALCHEMY_DATABASE_URI'] = "postgresql://postgres:postgres@localhost:5432/postgres"
app.config['SQLALCHEMY_TRACK_MODIFICATIONS'] = False
app.config['CACHE_TYPE'] = 'simple'
app.config['SESSION_TYPE'] = 'filesystem'
app.config['SESSION_PERMANENT'] = True
app.config['PERMANENT_SESSION_LIFETIME'] = 3600  # 1 hour
app.config['GOOGLE_CLIENT_ID'] = os.getenv('GOOGLE_CLIENT_ID', None)
app.config['GOOGLE_CLIENT_SECRET'] = os.getenv('GOOGLE_CLIENT_SECRET', None)
app.config['GOOGLE_DISCOVERY_URL'] = "https://accounts.google.com/.well-known/openid-configuration"
app.json.compact = False
# ------------------ App Config ------------------

# ------------------ Database ------------------
db = SQLAlchemy()
migrate = Migrate(app, db)
db.init_app(app)
# ------------------ Database ------------------

