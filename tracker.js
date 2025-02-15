// tracker.js
class VisitTracker {
    constructor() {
        this.storageKey = 'website_visits';
        this.todayKey = new Date().toISOString().split('T')[0];
    }

    // Load visits data from localStorage
    loadVisits() {
        try {
            return JSON.parse(localStorage.getItem(this.storageKey)) || {};
        } catch {
            return {};
        }
    }

    // Save visits data to localStorage
    saveVisits(visits) {
        localStorage.setItem(this.storageKey, JSON.stringify(visits));
    }

    // Record a new visit
    trackVisit() {
        const visits = this.loadVisits();
        
        // Initialize today's entry if it doesn't exist
        if (!visits[this.todayKey]) {
            visits[this.todayKey] = {
                total: 0,
                pages: {}
            };
        }

        // Increment total visits
        visits[this.todayKey].total++;

        // Track page visits
        const currentPage = window.location.pathname;
        visits[this.todayKey].pages[currentPage] = (visits[this.todayKey].pages[currentPage] || 0) + 1;

        // Save updated data
        this.saveVisits(visits);
    }

    // Get today's statistics
    getTodayStats() {
        const visits = this.loadVisits();
        const todayData = visits[this.todayKey] || { total: 0, pages: {} };
        
        return {
            date: this.todayKey,
            totalVisits: todayData.total,
            pageVisits: todayData.pages
        };
    }
}

// Initialize tracker
const tracker = new VisitTracker();

// Track visit when page loads
document.addEventListener('DOMContentLoaded', () => tracker.trackVisit());
