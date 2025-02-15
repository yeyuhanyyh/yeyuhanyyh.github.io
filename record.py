from datetime import datetime
import sqlite3
from flask import Flask, request

app = Flask(__name__)

def init_db():
    """Initialize SQLite database with visits table"""
    conn = sqlite3.connect('visits.db')
    c = conn.cursor()
    c.execute('''
        CREATE TABLE IF NOT EXISTS visits (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            timestamp DATETIME,
            ip_address TEXT,
            user_agent TEXT,
            page_url TEXT,
            referrer TEXT
        )
    ''')
    conn.commit()
    conn.close()

@app.before_first_request
def setup():
    init_db()

@app.route('/')
def track_visit():
    """Track each visit with detailed information"""
    # Get visit details
    visit_data = {
        'timestamp': datetime.now(),
        'ip_address': request.remote_addr,
        'user_agent': request.user_agent.string,
        'page_url': request.url,
        'referrer': request.referrer if request.referrer else ''
    }
    
    # Store in database
    conn = sqlite3.connect('visits.db')
    c = conn.cursor()
    c.execute('''
        INSERT INTO visits (timestamp, ip_address, user_agent, page_url, referrer)
        VALUES (?, ?, ?, ?, ?)
    ''', (
        visit_data['timestamp'],
        visit_data['ip_address'],
        visit_data['user_agent'],
        visit_data['page_url'],
        visit_data['referrer']
    ))
    conn.commit()
    conn.close()
    
    return 'Visit tracked'

@app.route('/stats')
def get_stats():
    """Get daily visit statistics"""
    conn = sqlite3.connect('visits.db')
    c = conn.cursor()
    
    # Get visits for the current day
    c.execute('''
        SELECT COUNT(*) as visit_count,
               COUNT(DISTINCT ip_address) as unique_visitors
        FROM visits
        WHERE date(timestamp) = date('now')
    ''')
    
    daily_stats = c.fetchone()
    conn.close()
    
    return {
        'total_visits': daily_stats[0],
        'unique_visitors': daily_stats[1],
        'date': datetime.now().date().isoformat()
    }

if __name__ == '__main__':
    app.run(debug=True)